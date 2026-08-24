import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 294` (rung-309; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT294 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((294 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((6689/62500 : ℚ) : ℝ))

theorem st294_c1 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((497139/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6689/250000) (δ := 1/1000000000) (ψ := 6689/62500) 294 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t1 : ((497089/500000 : ℚ) : ℝ) ≤ stT294 1 := by
  have hc : ((497089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497089/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((497089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c2 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-865181/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6540771/10000000) (δ := 14831/1000000000) (ψ := 6689/62500) 294 32
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t2 : ((-1529615197527/2500000000000 : ℚ) : ℝ) ≤ stT294 2 := by
  have hc : ((-865281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1529615197527/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-865281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c3 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-191361/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6106317/10000000) (δ := 2947/200000000) (ψ := 6689/62500) 294 51
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t3 : ((-552483822579/1250000000000 : ℚ) : ℝ) ≤ stT294 3 := by
  have hc : ((-95693/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552483822579/1250000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-95693/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c4 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((293467/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94353/400000) (δ := 923/62500000) (ψ := 6689/62500) 294 65
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t4 : ((293417/1000000 : ℚ) : ℝ) ≤ stT294 4 := by
  have hc : ((293417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293417/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((293417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c5 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-51037/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 571511/1250000) (δ := 14763/1000000000) (ψ := 6689/62500) 294 75
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t5 : ((-28541730969/250000000000 : ℚ) : ℝ) ≤ stT294 5 := by
  have hc : ((-51057/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28541730969/250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-51057/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c6 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((438101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2793279/10000000) (δ := 7399/500000000) (ψ := 6689/62500) 294 84
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t6 : ((894065599241/5000000000000 : ℚ) : ℝ) ≤ stT294 6 := by
  have hc : ((438001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((894065599241/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((438001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c7 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((195149/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 551743/10000000) (δ := 2951/200000000) (ψ := 6689/62500) 294 91
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t7 : ((184379538519/500000000000 : ℚ) : ℝ) ≤ stT294 7 := by
  have hc : ((195129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184379538519/500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((195129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c8 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-103751/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2224771/5000000) (δ := 2961/200000000) (ψ := 6689/62500) 294 97
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t8 : ((-183495982367/2500000000000 : ℚ) : ℝ) ≤ stT294 8 := by
  have hc : ((-103801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183495982367/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-103801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c9 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((276071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -806933/2500000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 103
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t9 : ((919903241343/10000000000000 : ℚ) : ℝ) ≤ stT294 9 := by
  have hc : ((275971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((919903241343/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((275971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c10 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-159551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4327581/10000000) (δ := 14777/1000000000) (ψ := 6689/62500) 294 108
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t10 : ((-252430422489/5000000000000 : ℚ) : ℝ) ≤ stT294 10 := by
  have hc : ((-159651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252430422489/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-159651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c11 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((401699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2893563/10000000) (δ := 7403/500000000) (ψ := 6689/62500) 294 112
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t11 : ((1210866365687/10000000000000 : ℚ) : ℝ) ≤ stT294 11 := by
  have hc : ((401599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1210866365687/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((401599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c12 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-1101/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4015089/10000000) (δ := 7417/500000000) (ψ := 6689/62500) 294 116
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t12 : ((-796833763/78125000000 : ℚ) : ℝ) ≤ stT294 12 := by
  have hc : ((-8833/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-796833763/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-8833/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c13 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((999983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731/500000) (δ := 737/50000000) (ψ := 6689/62500) 294 120
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t13 : ((5546351001/20000000000 : ℚ) : ℝ) ≤ stT294 13 := by
  have hc : ((999883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5546351001/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((999883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c14 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-980551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 736011/1000000) (δ := 7409/500000000) (ψ := 6689/62500) 294 123
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t14 : ((-2620900611063/10000000000000 : ℚ) : ℝ) ≤ stT294 14 := by
  have hc : ((-980651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2620900611063/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-980651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c15 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-327813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4761961/10000000) (δ := 14813/1000000000) (ψ := 6689/62500) 294 127
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t15 : ((-846667758957/10000000000000 : ℚ) : ℝ) ≤ stT294 15 := by
  have hc : ((-327913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-846667758957/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-327913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c16 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-103851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2225027/5000000) (δ := 3717/250000000) (ψ := 6689/62500) 294 130
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t16 : ((-259752603901/5000000000000 : ℚ) : ℝ) ≤ stT294 16 := by
  have hc : ((-103901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259752603901/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-103901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c17 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-944197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3507431/5000000) (δ := 1857/125000000) (ψ := 6689/62500) 294 133
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t17 : ((-2290257339029/10000000000000 : ℚ) : ℝ) ≤ stT294 17 := by
  have hc : ((-944297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2290257339029/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-944297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c18 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((1381/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 716127/2000000) (δ := 3683/250000000) (ψ := 6689/62500) 294 135
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t18 : ((81317259/2500000000 : ℚ) : ℝ) ≤ stT294 18 := by
  have hc : ((69/500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81317259/2500000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((69/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c19 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((49231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3803863/10000000) (δ := 14811/1000000000) (ψ := 6689/62500) 294 138
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t19 : ((112714227567/10000000000000 : ℚ) : ℝ) ≤ stT294 19 := by
  have hc : ((49131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112714227567/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((49131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c20 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((546753/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1240393/5000000) (δ := 3699/250000000) (ψ := 6689/62500) 294 140
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t20 : ((1222352733751/10000000000000 : ℚ) : ℝ) ≤ stT294 20 := by
  have hc : ((546653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1222352733751/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((546653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c21 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-465923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6925657/10000000) (δ := 14821/1000000000) (ψ := 6689/62500) 294 142
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t21 : ((-1016836495167/5000000000000 : ℚ) : ℝ) ≤ stT294 21 := by
  have hc : ((-465973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1016836495167/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-465973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c22 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-369511/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6006033/10000000) (δ := 14743/1000000000) (ψ := 6689/62500) 294 145
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t22 : ((-98488376061/625000000000 : ℚ) : ℝ) ≤ stT294 22 := by
  have hc : ((-369561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98488376061/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-369561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c23 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-323247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4749887/10000000) (δ := 7423/500000000) (ψ := 6689/62500) 294 147
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t23 : ((-134845076063/2000000000000 : ℚ) : ℝ) ≤ stT294 23 := by
  have hc : ((-323347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134845076063/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-323347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c24 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-373711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4884507/10000000) (δ := 14771/1000000000) (ψ := 6689/62500) 294 149
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t24 : ((-381519356631/5000000000000 : ℚ) : ℝ) ≤ stT294 24 := by
  have hc : ((-373811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381519356631/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-373811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c25 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-812081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -787033/1250000) (δ := 14817/1000000000) (ψ := 6689/62500) 294 151
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t25 : ((-1624362812181/10000000000000 : ℚ) : ℝ) ≤ stT294 25 := by
  have hc : ((-812181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1624362812181/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-812181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c26 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-916163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1705747/2500000) (δ := 14893/1000000000) (ψ := 6689/62500) 294 152
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t26 : ((-898470088803/5000000000000 : ℚ) : ℝ) ≤ stT294 26 := by
  have hc : ((-916263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-898470088803/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-916263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c27 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((307271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3146181/10000000) (δ := 931/62500000) (ψ := 6689/62500) 294 154
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t27 : ((1182301179/20000000000 : ℚ) : ℝ) ≤ stT294 27 := by
  have hc : ((307171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1182301179/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((307171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c28 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((163263/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -769743/5000000) (δ := 14881/1000000000) (ψ := 6689/62500) 294 156
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t28 : ((154250106373/1000000000000 : ℚ) : ℝ) ≤ stT294 28 := by
  have hc : ((163243/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154250106373/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((163243/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c29 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-6013/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7163307/10000000) (δ := 14867/1000000000) (ψ := 6689/62500) 294 158
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t29 : ((-44668099993/250000000000 : ℚ) : ℝ) ≤ stT294 29 := by
  have hc : ((-48109/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44668099993/250000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-48109/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c30 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((683293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2046333/10000000) (δ := 14843/1000000000) (ψ := 6689/62500) 294 159
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t30 : ((1247333471013/10000000000000 : ℚ) : ℝ) ≤ stT294 30 := by
  have hc : ((683193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1247333471013/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((683193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c31 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-255699/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5269017/10000000) (δ := 14857/1000000000) (ψ := 6689/62500) 294 161
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t31 : ((-229669507223/2500000000000 : ℚ) : ℝ) ≤ stT294 31 := by
  have hc : ((-255749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229669507223/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-255749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c32 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((587099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1179157/5000000) (δ := 2953/200000000) (ψ := 6689/62500) 294 162
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t32 : ((518838437117/5000000000000 : ℚ) : ℝ) ≤ stT294 32 := by
  have hc : ((586999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518838437117/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((586999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c33 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-105547/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6440487/10000000) (δ := 1853/125000000) (ψ := 6689/62500) 294 164
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t33 : ((-367511099463/2500000000000 : ℚ) : ℝ) ≤ stT294 33 := by
  have hc : ((-211119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367511099463/2500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-211119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c34 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((996591/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41299/2000000) (δ := 14717/1000000000) (ψ := 6689/62500) 294 165
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t34 : ((341793423527/2000000000000 : ℚ) : ℝ) ≤ stT294 34 := by
  have hc : ((996491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341793423527/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((996491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c35 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-552821/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2695677/5000000) (δ := 1481/100000000) (ψ := 6689/62500) 294 166
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t35 : ((-934607342589/10000000000000 : ℚ) : ℝ) ≤ stT294 35 := by
  have hc : ((-552921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-934607342589/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-552921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c36 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-264231/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5318961/10000000) (δ := 2959/200000000) (ψ := 6689/62500) 294 168
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t36 : ((-440468421427/5000000000000 : ℚ) : ℝ) ≤ stT294 36 := by
  have hc : ((-264281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-440468421427/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-264281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c37 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((187497/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -888659/10000000) (δ := 2943/200000000) (ψ := 6689/62500) 294 169
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t37 : ((308210125753/2000000000000 : ℚ) : ℝ) ≤ stT294 37 := by
  have hc : ((187477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308210125753/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((187477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c38 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((180339/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 600901/2000000) (δ := 7411/500000000) (ψ := 6689/62500) 294 170
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t38 : ((146233669923/2500000000000 : ℚ) : ℝ) ≤ stT294 38 := by
  have hc : ((180289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146233669923/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((180289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c39 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-41653/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3194267/5000000) (δ := 14729/1000000000) (ψ := 6689/62500) 294 171
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t39 : ((-16676551389/125000000000 : ℚ) : ℝ) ≤ stT294 39 := by
  have hc : ((-20829/25000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16676551389/125000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-20829/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c40 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-419849/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641881/1000000) (δ := 14859/1000000000) (ψ := 6689/62500) 294 173
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t40 : ((-663918684961/5000000000000 : ℚ) : ℝ) ≤ stT294 40 := by
  have hc : ((-419899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-663918684961/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-419899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c41 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-20287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -248607/625000) (δ := 461/31250000) (ψ := 6689/62500) 294 174
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t41 : ((-15919576303/5000000000000 : ℚ) : ℝ) ≤ stT294 41 := by
  have hc : ((-20387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15919576303/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-20387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c42 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((704147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1973939/10000000) (δ := 7379/500000000) (ψ := 6689/62500) 294 175
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t42 : ((1086367754551/10000000000000 : ℚ) : ℝ) ≤ stT294 42 := by
  have hc : ((704047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1086367754551/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((704047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c43 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((988043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77397/2000000) (δ := 7369/500000000) (ψ := 6689/62500) 294 176
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t43 : ((301319651171/2000000000000 : ℚ) : ℝ) ≤ stT294 43 := by
  have hc : ((987943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301319651171/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((987943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c44 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((948941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 401167/5000000) (δ := 14831/1000000000) (ψ := 6689/62500) 294 177
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t44 : ((357607735649/2500000000000 : ℚ) : ℝ) ≤ stT294 44 := by
  have hc : ((948841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((357607735649/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((948841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c45 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((799249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1611879/10000000) (δ := 3681/250000000) (ψ := 6689/62500) 294 178
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t45 : ((1191300204939/10000000000000 : ℚ) : ℝ) ≤ stT294 45 := by
  have hc : ((799149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1191300204939/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((799149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c46 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((679759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2058407/10000000) (δ := 463/31250000) (ψ := 6689/62500) 294 179
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t46 : ((1002102143121/10000000000000 : ℚ) : ℝ) ≤ stT294 46 := by
  have hc : ((679659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1002102143121/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((679659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c47 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((325069/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86303/400000) (δ := 7447/500000000) (ψ := 6689/62500) 294 180
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t47 : ((474088639331/5000000000000 : ℚ) : ℝ) ≤ stT294 47 := by
  have hc : ((325019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474088639331/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((325019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c48 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((179557/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96193/500000) (δ := 7401/500000000) (ψ := 6689/62500) 294 181
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t48 : ((518264001/5000000000 : ℚ) : ℝ) ≤ stT294 48 := by
  have hc : ((44883/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518264001/5000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((44883/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c49 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((426679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1371009/10000000) (δ := 3677/250000000) (ψ := 6689/62500) 294 182
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t49 : ((609469817159/5000000000000 : ℚ) : ℝ) ≤ stT294 49 := by
  have hc : ((426629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((609469817159/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((426629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c50 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((979093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64013/1250000) (δ := 2963/200000000) (ψ := 6689/62500) 294 183
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t50 : ((1384504627509/10000000000000 : ℚ) : ℝ) ≤ stT294 50 := by
  have hc : ((978993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1384504627509/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((978993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c51 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((483657/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -640949/10000000) (δ := 93/6250000) (ψ := 6689/62500) 294 184
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t51 : ((16929630249/125000000000 : ℚ) : ℝ) ≤ stT294 51 := by
  have hc : ((483607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16929630249/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((483607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c52 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((674401/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32447/156250) (δ := 1483/100000000) (ψ := 6689/62500) 294 185
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t52 : ((3740347647/40000000000 : ℚ) : ℝ) ≤ stT294 52 := by
  have hc : ((674301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3740347647/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((674301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c53 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((57107/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -756829/2000000) (δ := 7433/500000000) (ψ := 6689/62500) 294 186
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t53 : ((15661020047/2000000000000 : ℚ) : ℝ) ≤ stT294 53 := by
  have hc : ((57007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15661020047/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((57007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c54 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-333647/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2876707/5000000) (δ := 3711/250000000) (ψ := 6689/62500) 294 187
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t54 : ((-113526055279/1250000000000 : ℚ) : ℝ) ≤ stT294 54 := by
  have hc : ((-333697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113526055279/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-333697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c55 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-998833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3866587/5000000) (δ := 14759/1000000000) (ψ := 6689/62500) 294 187
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t55 : ((-3367403143/25000000000 : ℚ) : ℝ) ≤ stT294 55 := by
  have hc : ((-998933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3367403143/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-998933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c56 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-255663/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658601/1250000) (δ := 3713/250000000) (ψ := 6689/62500) 294 188
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t56 : ((-341711071891/5000000000000 : ℚ) : ℝ) ≤ stT294 56 := by
  have hc : ((-255713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341711071891/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-255713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c57 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((103303/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2570051/10000000) (δ := 2949/200000000) (ψ := 6689/62500) 294 189
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t57 : ((34200409639/500000000000 : ℚ) : ℝ) ≤ stT294 57 := by
  have hc : ((103283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34200409639/500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((103283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c58 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((494969/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -354939/10000000) (δ := 7383/500000000) (ψ := 6689/62500) 294 190
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t58 : ((81232540227/625000000000 : ℚ) : ℝ) ≤ stT294 58 := by
  have hc : ((494919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81232540227/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((494919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c59 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((170551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1749259/5000000) (δ := 14873/1000000000) (ψ := 6689/62500) 294 191
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t59 : ((221908281939/10000000000000 : ℚ) : ℝ) ≤ stT294 59 := by
  have hc : ((170451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221908281939/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((170451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c60 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-920949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6853263/10000000) (δ := 739/50000000) (ψ := 6689/62500) 294 192
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t60 : ((-237813930751/2000000000000 : ℚ) : ℝ) ≤ stT294 60 := by
  have hc : ((-921049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237813930751/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-921049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c61 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-104113/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1323943/2500000) (δ := 14823/1000000000) (ψ := 6689/62500) 294 192
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t61 : ((-133328665077/2000000000000 : ℚ) : ℝ) ≤ stT294 61 := by
  have hc : ((-104133/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133328665077/2000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-104133/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c62 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((816363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1539277/10000000) (δ := 14887/1000000000) (ψ := 6689/62500) 294 193
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t62 : ((1036654826263/10000000000000 : ℚ) : ℝ) ≤ stT294 62 := by
  have hc : ((816263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1036654826263/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((816263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c63 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((570767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2408393/10000000) (δ := 14809/1000000000) (ψ := 6689/62500) 294 194
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t63 : ((718972510627/10000000000000 : ℚ) : ℝ) ≤ stT294 63 := by
  have hc : ((570667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718972510627/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((570667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c64 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-865299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1635339/2500000) (δ := 14901/1000000000) (ψ := 6689/62500) 294 195
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t64 : ((-1081749615399/10000000000000 : ℚ) : ℝ) ≤ stT294 64 := by
  have hc : ((-865399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1081749615399/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-865399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c65 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-362451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4854231/10000000) (δ := 14901/1000000000) (ψ := 6689/62500) 294 195
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t65 : ((-112422351937/2500000000000 : ℚ) : ℝ) ≤ stT294 65 := by
  have hc : ((-362551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112422351937/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-362551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c66 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((989193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 367881/10000000) (δ := 14809/1000000000) (ψ := 6689/62500) 294 196
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t66 : ((608744210501/5000000000000 : ℚ) : ℝ) ≤ stT294 66 := by
  have hc : ((989093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((608744210501/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((989093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c67 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-35899/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2143613/5000000) (δ := 3679/250000000) (ψ := 6689/62500) 294 197
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t67 : ((-2194408559/125000000000 : ℚ) : ℝ) ≤ stT294 67 := by
  have hc : ((-8981/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2194408559/125000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-8981/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c68 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-438589/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412617/625000) (δ := 14887/1000000000) (ψ := 6689/62500) 294 197
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t68 : ((-531928303881/5000000000000 : ℚ) : ℝ) ≤ stT294 68 := by
  have hc : ((-438639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-531928303881/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-438639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c69 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((796319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1624027/10000000) (δ := 739/50000000) (ψ := 6689/62500) 294 198
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t69 : ((479267306451/5000000000000 : ℚ) : ℝ) ≤ stT294 69 := by
  have hc : ((796219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((479267306451/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((796219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c70 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((166717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1754121/5000000) (δ := 14873/1000000000) (ψ := 6689/62500) 294 199
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t70 : ((49786325919/2500000000000 : ℚ) : ℝ) ≤ stT294 70 := by
  have hc : ((166617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49786325919/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((166617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c71 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-116331/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6917439/10000000) (δ := 14873/1000000000) (ψ := 6689/62500) 294 199
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t71 : ((-138074371617/1250000000000 : ℚ) : ℝ) ≤ stT294 71 := by
  have hc : ((-232687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138074371617/1250000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-232687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c72 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((827721/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1489407/10000000) (δ := 14837/1000000000) (ψ := 6689/62500) 294 200
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t72 : ((975360452331/10000000000000 : ℚ) : ℝ) ≤ stT294 72 := by
  have hc : ((827621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((975360452331/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((827621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c73 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-30679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4080481/10000000) (δ := 2949/200000000) (ψ := 6689/62500) 294 201
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t73 : ((-8991397587/1250000000000 : ℚ) : ℝ) ≤ stT294 73 := by
  have hc : ((-30729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8991397587/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-30729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c74 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-715303/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1183927/2000000) (δ := 2949/200000000) (ψ := 6689/62500) 294 201
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t74 : ((-831639533231/10000000000000 : ℚ) : ℝ) ≤ stT294 74 := by
  have hc : ((-715403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-831639533231/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-715403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c75 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((499759/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1553/200000) (δ := 14751/1000000000) (ψ := 6689/62500) 294 202
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t75 : ((5770139823/50000000000 : ℚ) : ℝ) ≤ stT294 75 := by
  have hc : ((499709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5770139823/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((499709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c76 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-88551/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5895091/10000000) (δ := 14759/1000000000) (ψ := 6689/62500) 294 203
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t76 : ((-203178662033/2500000000000 : ℚ) : ℝ) ≤ stT294 76 := by
  have hc : ((-177127/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203178662033/2500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-177127/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c77 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((85531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1856451/5000000) (δ := 3711/250000000) (ψ := 6689/62500) 294 203
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t77 : ((19471518951/2000000000000 : ℚ) : ℝ) ≤ stT294 77 := by
  have hc : ((85431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19471518951/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((85431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c78 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((268287/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1255531/5000000) (δ := 14737/1000000000) (ψ := 6689/62500) 294 204
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t78 : ((303718585649/5000000000000 : ℚ) : ℝ) ≤ stT294 78 := by
  have hc : ((268237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303718585649/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((268237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c79 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-14387/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6852103/10000000) (δ := 14737/1000000000) (ψ := 6689/62500) 294 204
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t79 : ((-8094199503/78125000000 : ℚ) : ℝ) ≤ stT294 79 := by
  have hc : ((-230217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8094199503/78125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-230217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c80 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((246971/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194779/5000000) (δ := 14773/1000000000) (ψ := 6689/62500) 294 205
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t80 : ((138046888609/1250000000000 : ℚ) : ℝ) ≤ stT294 80 := by
  have hc : ((123473/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138046888609/1250000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((123473/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c81 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-98253/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1546967/2500000) (δ := 14723/1000000000) (ψ := 6689/62500) 294 206
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t81 : ((-27295994059/312500000000 : ℚ) : ℝ) ≤ stT294 81 := by
  have hc : ((-196531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27295994059/312500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-196531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c82 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((424613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44229/156250) (δ := 93/6250000) (ψ := 6689/62500) 294 206
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t82 : ((93759214719/2000000000000 : ℚ) : ℝ) ≤ stT294 82 := by
  have hc : ((424513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93759214719/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((424513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c83 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-3287/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3968079/10000000) (δ := 2963/200000000) (ψ := 6689/62500) 294 207
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t83 : ((-3629905401/2000000000000 : ℚ) : ℝ) ≤ stT294 83 := by
  have hc : ((-3307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3629905401/2000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-3307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c84 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-355043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604299/1250000) (δ := 7397/250000000) (ψ := 6689/62500) 294 207
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t84 : ((-38749297587/1000000000000 : ℚ) : ℝ) ≤ stT294 84 := by
  have hc : ((-355143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38749297587/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-355143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c85 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((2579/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2175251/10000000) (δ := 3677/250000000) (ψ := 6689/62500) 294 208
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t85 : ((3496104559/50000000000 : ℚ) : ℝ) ≤ stT294 85 := by
  have hc : ((12893/20000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3496104559/50000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((12893/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c86 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-840241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6421309/10000000) (δ := 3677/250000000) (ψ := 6689/62500) 294 208
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t86 : ((-113270403731/1250000000000 : ℚ) : ℝ) ≤ stT294 86 := by
  have hc : ((-840341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113270403731/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-840341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c87 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((475281/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789393/10000000) (δ := 14801/1000000000) (ψ := 6689/62500) 294 209
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t87 : ((31843803617/312500000000 : ℚ) : ℝ) ≤ stT294 87 := by
  have hc : ((475231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31843803617/312500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((475231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c88 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-995269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3805351/5000000) (δ := 7401/500000000) (ψ := 6689/62500) 294 209
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t88 : ((-265266833869/2500000000000 : ℚ) : ℝ) ≤ stT294 88 := by
  have hc : ((-995369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265266833869/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-995369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c89 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((199309/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207871/10000000) (δ := 14709/1000000000) (ψ := 6689/62500) 294 210
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t89 : ((211245742133/2000000000000 : ℚ) : ℝ) ≤ stT294 89 := by
  have hc : ((199289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211245742133/2000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((199289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c90 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-974457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7287717/10000000) (δ := 14787/1000000000) (ψ := 6689/62500) 294 211
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t90 : ((-1027273711801/10000000000000 : ℚ) : ℝ) ≤ stT294 90 := by
  have hc : ((-974557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1027273711801/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-974557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c91 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((11811/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 833923/10000000) (δ := 3677/125000000) (ψ := 6689/62500) 294 211
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t91 : ((12379971969/125000000000 : ℚ) : ℝ) ≤ stT294 91 := by
  have hc : ((47239/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12379971969/125000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((47239/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c92 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-57441/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6841189/10000000) (δ := 14879/1000000000) (ψ := 6689/62500) 294 212
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t92 : ((-239571807097/2500000000000 : ℚ) : ℝ) ≤ stT294 92 := by
  have hc : ((-229789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239571807097/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-229789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c93 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((112991/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1104823/10000000) (δ := 3681/250000000) (ψ := 6689/62500) 294 212
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t93 : ((234306337107/2500000000000 : ℚ) : ℝ) ≤ stT294 93 := by
  have hc : ((225957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234306337107/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((225957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c94 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-225679/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1348419/2000000) (δ := 3693/250000000) (ψ := 6689/62500) 294 213
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t94 : ((-14549754443/156250000000 : ℚ) : ℝ) ≤ stT294 94 := by
  have hc : ((-28213/31250 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14549754443/156250000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-28213/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c95 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((457699/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1035749/10000000) (δ := 14831/1000000000) (ψ := 6689/62500) 294 213
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t95 : ((234768902861/2500000000000 : ℚ) : ℝ) ≤ stT294 95 := by
  have hc : ((457649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234768902861/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((457649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c96 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-938937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6975809/10000000) (δ := 7369/500000000) (ψ := 6689/62500) 294 214
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t96 : ((-958400881977/10000000000000 : ℚ) : ℝ) ≤ stT294 96 := by
  have hc : ((-939037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-958400881977/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-939037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c97 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((38693/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 640849/10000000) (δ := 7369/500000000) (ψ := 6689/62500) 294 214
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t97 : ((19641360697/200000000000 : ℚ) : ℝ) ≤ stT294 97 := by
  have hc : ((38689/40000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19641360697/200000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((38689/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c98 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-991541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7528587/10000000) (δ := 7379/500000000) (ψ := 6689/62500) 294 215
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t98 : ((-1001709131073/10000000000000 : ℚ) : ℝ) ≤ stT294 98 := by
  have hc : ((-991641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1001709131073/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-991641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c99 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((199929/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66573/10000000) (δ := 7379/500000000) (ψ := 6689/62500) 294 215
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t99 : ((200915941633/2000000000000 : ℚ) : ℝ) ≤ stT294 99 := by
  have hc : ((199909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200915941633/2000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((199909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c100 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-977309/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3660199/5000000) (δ := 2969/200000000) (ψ := 6689/62500) 294 215
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t100 : ((-977409/10000000 : ℚ) : ℝ) ≤ stT294 100 := by
  have hc : ((-977409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-977409/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-977409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c101 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((909129/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -537011/5000000) (δ := 14851/1000000000) (ψ := 6689/62500) 294 216
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t101 : ((904517489073/10000000000000 : ℚ) : ℝ) ≤ stT294 101 := by
  have hc : ((909029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((904517489073/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((909029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c102 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-780941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6167419/10000000) (δ := 461/31250000) (ψ := 6689/62500) 294 216
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t102 : ((-193336546017/2500000000000 : ℚ) : ℝ) ≤ stT294 102 := by
  have hc : ((-781041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193336546017/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-781041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c103 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((58337/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2369811/10000000) (δ := 1843/125000000) (ψ := 6689/62500) 294 217
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t103 : ((57471284583/1000000000000 : ℚ) : ℝ) ≤ stT294 103 := by
  have hc : ((58327/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57471284583/1000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((58327/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c104 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-316349/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2365843/5000000) (δ := 14859/1000000000) (ψ := 6689/62500) 294 217
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t104 : ((-310303876869/10000000000000 : ℚ) : ℝ) ≤ stT294 104 := by
  have hc : ((-316449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310303876869/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-316449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c105 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-3141/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -788539/2000000) (δ := 14767/1000000000) (ψ := 6689/62500) 294 218
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t105 : ((-3114100091/5000000000000 : ℚ) : ℝ) ≤ stT294 105 := by
  have hc : ((-3191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3114100091/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-3191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c106 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((176669/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3024149/10000000) (δ := 3709/250000000) (ψ := 6689/62500) 294 218
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t106 : ((34309477083/1000000000000 : ℚ) : ℝ) ≤ stT294 106 := by
  have hc : ((176619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34309477083/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((176619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c107 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-337929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5782311/10000000) (δ := 14729/1000000000) (ψ := 6689/62500) 294 219
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t107 : ((-326736804523/5000000000000 : ℚ) : ℝ) ≤ stT294 107 := by
  have hc : ((-337979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326736804523/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-337979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c108 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((912279/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1054953/10000000) (δ := 14729/1000000000) (ψ := 6689/62500) 294 219
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t108 : ((3510976971/40000000000 : ℚ) : ℝ) ≤ stT294 108 := by
  have hc : ((912179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3510976971/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((912179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c109 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-999951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3914577/5000000) (δ := 14729/1000000000) (ψ := 6689/62500) 294 219
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t109 : ((-957875849177/10000000000000 : ℚ) : ℝ) ≤ stT294 109 := by
  have hc : ((-1000051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-957875849177/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-1000051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c110 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((893117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -583211/5000000) (δ := 7411/500000000) (ψ := 6689/62500) 294 220
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t110 : ((425728887427/5000000000000 : ℚ) : ℝ) ≤ stT294 110 := by
  have hc : ((893017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((425728887427/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((893017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c111 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-291861/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1097051/2000000) (δ := 14781/1000000000) (ψ := 6689/62500) 294 220
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t111 : ((-138534830469/2500000000000 : ℚ) : ℝ) ≤ stT294 111 := by
  have hc : ((-291911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138534830469/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-291911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c112 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((23641/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3630787/10000000) (δ := 1861/125000000) (ψ := 6689/62500) 294 221
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t112 : ((22319742731/2000000000000 : ℚ) : ℝ) ≤ stT294 112 := by
  have hc : ((23621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22319742731/2000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((23621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c113 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((49797/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725657/2500000) (δ := 1861/125000000) (ψ := 6689/62500) 294 221
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t113 : ((1170831871/31250000000 : ℚ) : ℝ) ≤ stT294 113 := by
  have hc : ((99569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1170831871/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((99569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c114 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-819777/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1265909/2000000) (δ := 1851/125000000) (ψ := 6689/62500) 294 222
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t114 : ((-383942659961/5000000000000 : ℚ) : ℝ) ≤ stT294 114 := by
  have hc : ((-819877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383942659961/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-819877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c115 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((249839/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3589/400000) (δ := 2959/200000000) (ψ := 6689/62500) 294 222
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t115 : ((14559534641/156250000000 : ℚ) : ℝ) ≤ stT294 115 := by
  have hc : ((124907/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14559534641/156250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((124907/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c116 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-423561/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1290671/2000000) (δ := 2959/200000000) (ψ := 6689/62500) 294 222
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t116 : ((-393313070447/5000000000000 : ℚ) : ℝ) ≤ stT294 116 := by
  have hc : ((-423611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393313070447/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-423611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c117 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((382583/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -736379/2500000) (δ := 149/10000000) (ψ := 6689/62500) 294 223
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t117 : ((707211067/20000000000 : ℚ) : ℝ) ≤ stT294 117 := by
  have hc : ((382483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((707211067/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((382483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c118 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((244357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3309849/10000000) (δ := 14703/1000000000) (ψ := 6689/62500) 294 223
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t118 : ((112428321759/5000000000000 : ℚ) : ℝ) ≤ stT294 118 := by
  have hc : ((244257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112428321759/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((244257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c119 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-787931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1548899/2500000) (δ := 1481/100000000) (ψ := 6689/62500) 294 224
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t119 : ((-722387229669/10000000000000 : ℚ) : ℝ) ≤ stT294 119 := by
  have hc : ((-788031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-722387229669/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-788031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c120 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((999839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1403/312500) (δ := 14793/1000000000) (ψ := 6689/62500) 294 224
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t120 : ((91263174093/1000000000000 : ℚ) : ℝ) ≤ stT294 120 := by
  have hc : ((999739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91263174093/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((999739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c121 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-752001/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3027361/5000000) (δ := 14793/1000000000) (ψ := 6689/62500) 294 224
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t121 : ((-683728250191/10000000000000 : ℚ) : ℝ) ≤ stT294 121 := by
  have hc : ((-752101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-683728250191/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-752101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c122 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((128907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225239/625000) (δ := 7443/500000000) (ψ := 6689/62500) 294 225
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t122 : ((116616319099/10000000000000 : ℚ) : ℝ) ≤ stT294 122 := by
  have hc : ((128807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116616319099/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((128807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c123 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((143691/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1198101/5000000) (δ := 14717/1000000000) (ψ := 6689/62500) 294 225
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t123 : ((64769589277/1250000000000 : ℚ) : ℝ) ≤ stT294 123 := by
  have hc : ((71833/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64769589277/1250000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((71833/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c124 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-980567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7360319/10000000) (δ := 1853/125000000) (ψ := 6689/62500) 294 226
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t124 : ((-880665444009/10000000000000 : ℚ) : ℝ) ≤ stT294 124 := by
  have hc : ((-980667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-880665444009/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-980667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c125 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((417501/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -364163/2500000) (δ := 1853/125000000) (ψ := 6689/62500) 294 226
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t125 : ((373379445577/5000000000000 : ℚ) : ℝ) ≤ stT294 125 := by
  have hc : ((417451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373379445577/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((417451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c126 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-188067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175999/400000) (δ := 1853/125000000) (ψ := 6689/62500) 294 226
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t126 : ((-167632523457/10000000000000 : ℚ) : ℝ) ≤ stT294 126 := by
  have hc : ((-188167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167632523457/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-188167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c127 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-58777/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274887/500000) (δ := 14731/1000000000) (ψ := 6689/62500) 294 227
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t127 : ((-52165055959/1000000000000 : ℚ) : ℝ) ≤ stT294 127 := by
  have hc : ((-58787/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52165055959/1000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-58787/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c128 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((497151/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66753/2500000) (δ := 14731/1000000000) (ψ := 6689/62500) 294 227
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t128 : ((439379123183/5000000000000 : ℚ) : ℝ) ≤ stT294 128 := by
  have hc : ((497101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439379123183/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((497101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c129 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-183463/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5986929/10000000) (δ := 14731/1000000000) (ψ := 6689/62500) 294 227
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t129 : ((-2524253017/39062500000 : ℚ) : ℝ) ≤ stT294 129 := by
  have hc : ((-11468/15625 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2524253017/39062500000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-11468/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c130 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-11833/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011341/2500000) (δ := 7419/500000000) (ψ := 6689/62500) 294 228
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t130 : ((-5200082811/1250000000000 : ℚ) : ℝ) ≤ stT294 130 := by
  have hc : ((-5929/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5200082811/1250000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-5929/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c131 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((402611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1586867/10000000) (δ := 2953/200000000) (ψ := 6689/62500) 294 228
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t131 : ((43964894493/625000000000 : ℚ) : ℝ) ≤ stT294 131 := by
  have hc : ((402561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43964894493/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((402561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c132 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-963479/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897031/1250000) (δ := 2953/200000000) (ψ := 6689/62500) 294 228
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t132 : ((-838688562231/10000000000000 : ℚ) : ℝ) ≤ stT294 132 := by
  have hc : ((-963579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-838688562231/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-963579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c133 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((368121/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2984523/10000000) (δ := 7373/500000000) (ψ := 6689/62500) 294 229
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t133 : ((319114321289/10000000000000 : ℚ) : ℝ) ≤ stT294 133 := by
  have hc : ((368021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319114321289/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((368021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c134 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((533179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504221/2000000) (δ := 14773/500000000) (ψ := 6689/62500) 294 229
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t134 : ((115127472393/2500000000000 : ℚ) : ℝ) ≤ stT294 134 := by
  have hc : ((533079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115127472393/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((533079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c135 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-99861/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772217/1000000) (δ := 14853/1000000000) (ψ := 6689/62500) 294 230
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t135 : ((-85955274473/1000000000000 : ℚ) : ℝ) ≤ stT294 135 := by
  have hc : ((-99871/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85955274473/1000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-99871/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c136 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((606521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2297797/10000000) (δ := 59/4000000) (ψ := 6689/62500) 294 230
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t136 : ((130000289033/2500000000000 : ℚ) : ℝ) ≤ stT294 136 := by
  have hc : ((606421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130000289033/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((606421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c137 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((329753/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3086887/10000000) (δ := 14853/1000000000) (ψ := 6689/62500) 294 230
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t137 : ((281641348121/10000000000000 : ℚ) : ℝ) ≤ stT294 137 := by
  have hc : ((329653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281641348121/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((329653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c138 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-973361/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3637821/5000000) (δ := 369/25000000) (ψ := 6689/62500) 294 231
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t138 : ((-828665490477/10000000000000 : ℚ) : ℝ) ≤ stT294 138 := by
  have hc : ((-973461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-828665490477/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-973461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c139 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((705627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -984361/5000000) (δ := 14843/1000000000) (ψ := 6689/62500) 294 231
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t139 : ((149604883769/2500000000000 : ℚ) : ℝ) ≤ stT294 139 := by
  have hc : ((705527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149604883769/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((705527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c140 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((248127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1650063/5000000) (δ := 369/25000000) (ψ := 6689/62500) 294 231
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t140 : ((104810505579/5000000000000 : ℚ) : ℝ) ≤ stT294 140 := by
  have hc : ((248027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104810505579/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((248027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c141 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-963511/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1794137/2500000) (δ := 14867/1000000000) (ψ := 6689/62500) 294 232
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t141 : ((-101438366359/1250000000000 : ℚ) : ℝ) ≤ stT294 141 := by
  have hc : ((-963611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101438366359/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-963611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c142 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((701809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495539/2500000) (δ := 14867/1000000000) (ψ := 6689/62500) 294 232
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t142 : ((588860860329/10000000000000 : ℚ) : ℝ) ≤ stT294 142 := by
  have hc : ((701709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((588860860329/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((701709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c143 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((295983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158789/500000) (δ := 14867/1000000000) (ψ := 6689/62500) 294 232
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t143 : ((123714895843/5000000000000 : ℚ) : ℝ) ≤ stT294 143 := by
  have hc : ((295883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123714895843/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((295883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c144 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-98429/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7410263/10000000) (δ := 14829/1000000000) (ψ := 6689/62500) 294 233
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t144 : ((-41016282813/500000000000 : ℚ) : ℝ) ≤ stT294 144 := by
  have hc : ((-98439/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41016282813/500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-98439/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c145 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((149563/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -464739/2000000) (δ := 7387/500000000) (ψ := 6689/62500) 294 233
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t145 : ((31046107563/625000000000 : ℚ) : ℝ) ≤ stT294 145 := by
  have hc : ((74769/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31046107563/625000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((74769/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c146 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((230731/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1363943/5000000) (δ := 14829/1000000000) (ψ := 6689/62500) 294 233
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t146 : ((38182549801/1000000000000 : ℚ) : ℝ) ≤ stT294 146 := by
  have hc : ((230681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38182549801/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((230681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c147 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-999049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7744923/10000000) (δ := 7387/500000000) (ψ := 6689/62500) 294 233
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t147 : ((-824085106263/10000000000000 : ℚ) : ℝ) ≤ stT294 147 := by
  have hc : ((-999149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-824085106263/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-999149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c148 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((369817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2979961/10000000) (δ := 14721/1000000000) (ψ := 6689/62500) 294 234
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t148 : ((151952577849/5000000000000 : ℚ) : ℝ) ≤ stT294 148 := by
  have hc : ((369717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151952577849/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((369717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c149 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((705377/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1969603/10000000) (δ := 7441/500000000) (ψ := 6689/62500) 294 234
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t149 : ((577784781987/10000000000000 : ℚ) : ℝ) ≤ stT294 149 := by
  have hc : ((705277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((577784781987/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((705277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c150 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-231491/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 860743/1250000) (δ := 14721/1000000000) (ψ := 6689/62500) 294 234
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t150 : ((-47258029863/625000000000 : ℚ) : ℝ) ≤ stT294 150 := by
  have hc : ((-57879/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47258029863/625000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-57879/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c151 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-4499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1969119/5000000) (δ := 14789/1000000000) (ψ := 6689/62500) 294 235
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t151 : ((-3742615611/10000000000000 : ℚ) : ℝ) ≤ stT294 151 := by
  have hc : ((-4599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3742615611/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-4599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c152 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((934013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228319/2500000) (δ := 7407/500000000) (ψ := 6689/62500) 294 235
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t152 : ((757503371691/10000000000000 : ℚ) : ℝ) ≤ stT294 152 := by
  have hc : ((933913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((757503371691/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((933913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c153 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-661179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1146593/2000000) (δ := 7407/500000000) (ψ := 6689/62500) 294 235
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t153 : ((-534612991387/10000000000000 : ℚ) : ℝ) ≤ stT294 153 := by
  have hc : ((-661279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534612991387/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-661279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c154 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-120707/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5186693/10000000) (δ := 931/62500000) (ψ := 6689/62500) 294 236
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t154 : ((-24322155609/625000000000 : ℚ) : ℝ) ≤ stT294 154 := by
  have hc : ((-30183/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24322155609/625000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-30183/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c155 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((197057/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214703/5000000) (δ := 14707/1000000000) (ψ := 6689/62500) 294 236
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t155 : ((158263862103/2000000000000 : ℚ) : ℝ) ≤ stT294 155 := by
  have hc : ((197037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158263862103/2000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((197037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c156 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-29517/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2148653/5000000) (δ := 931/62500000) (ψ := 6689/62500) 294 236
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t156 : ((-23648533217/2000000000000 : ℚ) : ℝ) ≤ stT294 156 := by
  have hc : ((-29537/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23648533217/2000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-29537/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c157 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-224463/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1342831/2000000) (δ := 37/2500000) (ψ := 6689/62500) 294 237
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t157 : ((-22395119307/312500000000 : ℚ) : ℝ) ≤ stT294 157 := by
  have hc : ((-28061/31250 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22395119307/312500000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-28061/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c158 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((341477/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2047493/10000000) (δ := 37/2500000) (ψ := 6689/62500) 294 237
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t158 : ((271624639839/5000000000000 : ℚ) : ℝ) ≤ stT294 158 := by
  have hc : ((341427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271624639839/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((341427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c159 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((101949/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2589769/10000000) (δ := 37/2500000) (ψ := 6689/62500) 294 237
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t159 : ((80834895379/2000000000000 : ℚ) : ℝ) ≤ stT294 159 := by
  have hc : ((101929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80834895379/2000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((101929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c160 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-241441/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287917/400000) (δ := 37/2500000) (ψ := 6689/62500) 294 237
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t160 : ((-9544788781/125000000000 : ℚ) : ℝ) ≤ stT294 160 := by
  have hc : ((-120733/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9544788781/125000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-120733/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c161 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3930621/10000000) (δ := 14893/1000000000) (ψ := 6689/62500) 294 238
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t161 : ((-76446767/625000000000 : ℚ) : ℝ) ≤ stT294 161 := by
  have hc : ((-97/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76446767/625000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-97/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c162 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((242339/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 620499/10000000) (δ := 14893/1000000000) (ψ := 6689/62500) 294 238
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t162 : ((47594952409/625000000000 : ℚ) : ℝ) ≤ stT294 162 := by
  have hc : ((121157/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47594952409/625000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((121157/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c163 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-116917/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80369/156250) (δ := 1471/100000000) (ψ := 6689/62500) 294 238
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t163 : ((-45798053931/1250000000000 : ℚ) : ℝ) ≤ stT294 163 := by
  have hc : ((-58471/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45798053931/1250000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-58471/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c164 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-377869/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303447/500000) (δ := 14817/1000000000) (ψ := 6689/62500) 294 239
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t164 : ((-295105231611/5000000000000 : ℚ) : ℝ) ≤ stT294 164 := by
  have hc : ((-377919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295105231611/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-377919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c165 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((801887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12807/80000) (δ := 14817/1000000000) (ψ := 6689/62500) 294 239
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t165 : ((312094787963/5000000000000 : ℚ) : ℝ) ≤ stT294 165 := by
  have hc : ((801787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312094787963/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((801787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c166 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((105287/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568043/2000000) (δ := 7393/500000000) (ψ := 6689/62500) 294 239
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t166 : ((816991013/25000000000 : ℚ) : ℝ) ≤ stT294 166 := by
  have hc : ((52631/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((816991013/25000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((52631/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c167 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-485703/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7254699/10000000) (δ := 14817/1000000000) (ψ := 6689/62500) 294 239
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t167 : ((-5873239523/78125000000 : ℚ) : ℝ) ≤ stT294 167 := by
  have hc : ((-485753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5873239523/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-485753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c168 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-6909/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4065241/10000000) (δ := 589/40000000) (ψ := 6689/62500) 294 240
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t168 : ((-10680109831/2500000000000 : ℚ) : ℝ) ≤ stT294 168 := by
  have hc : ((-13843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10680109831/2500000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-13843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c169 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((992959/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296837/10000000) (δ := 589/40000000) (ψ := 6689/62500) 294 240
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t169 : ((76373692857/1000000000000 : ℚ) : ℝ) ≤ stT294 169 := by
  have hc : ((992859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76373692857/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((992859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c170 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-278709/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1158279/2500000) (δ := 7439/500000000) (ψ := 6689/62500) 294 240
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t170 : ((-42767348937/2000000000000 : ℚ) : ℝ) ≤ stT294 170 := by
  have hc : ((-278809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42767348937/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-278809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c171 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-906451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3381999/5000000) (δ := 927/62500000) (ψ := 6689/62500) 294 241
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t171 : ((-8665721009/125000000000 : ℚ) : ℝ) ≤ stT294 171 := by
  have hc : ((-906551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8665721009/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-906551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c172 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((54759/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2478287/10000000) (δ := 14771/1000000000) (ψ := 6689/62500) 294 241
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t172 : ((10436418627/250000000000 : ℚ) : ℝ) ≤ stT294 172 := by
  have hc : ((54749/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10436418627/250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((54749/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c173 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((378191/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 891291/5000000) (δ := 927/62500000) (ψ := 6689/62500) 294 241
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t173 : ((57498986037/1000000000000 : ℚ) : ℝ) ≤ stT294 173 := by
  have hc : ((378141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57498986037/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((378141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c174 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-742479/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6018901/10000000) (δ := 14771/1000000000) (ψ := 6689/62500) 294 241
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t174 : ((-562948397321/10000000000000 : ℚ) : ℝ) ≤ stT294 174 := by
  have hc : ((-742579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562948397321/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-742579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c175 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-581037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2738499/5000000) (δ := 929/62500000) (ψ := 6689/62500) 294 242
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t175 : ((-439298311273/10000000000000 : ℚ) : ℝ) ≤ stT294 175 := by
  have hc : ((-581137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439298311273/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-581137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c176 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((870003/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161121/1250000) (δ := 929/62500000) (ψ := 6689/62500) 294 242
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t176 : ((327856871767/5000000000000 : ℚ) : ℝ) ≤ stT294 176 := by
  have hc : ((869903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327856871767/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((869903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c177 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((408343/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 575079/2000000) (δ := 929/62500000) (ψ := 6689/62500) 294 242
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t177 : ((153427108989/5000000000000 : ℚ) : ℝ) ≤ stT294 177 := by
  have hc : ((408243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153427108989/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((408243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c178 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-472189/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3508119/5000000) (δ := 929/62500000) (ψ := 6689/62500) 294 242
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t178 : ((-88489560537/1250000000000 : ℚ) : ℝ) ≤ stT294 178 := by
  have hc : ((-472239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88489560537/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-472239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c179 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-255937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2287017/5000000) (δ := 7423/500000000) (ψ := 6689/62500) 294 243
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t179 : ((-47842817783/2500000000000 : ℚ) : ℝ) ≤ stT294 179 := by
  have hc : ((-256037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47842817783/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-256037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c180 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((490837/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479349/10000000) (δ := 7423/500000000) (ψ := 6689/62500) 294 243
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t180 : ((73162108877/1000000000000 : ℚ) : ℝ) ≤ stT294 180 := by
  have hc : ((490787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73162108877/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((490787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c181 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((133319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1796349/5000000) (δ := 7423/500000000) (ψ := 6689/62500) 294 243
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t181 : ((49510441693/5000000000000 : ℚ) : ℝ) ≤ stT294 181 := by
  have hc : ((133219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49510441693/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((133219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c182 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-15569/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3821127/5000000) (δ := 7423/500000000) (ψ := 6689/62500) 294 243
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t182 : ((-147733497/2000000000 : ℚ) : ℝ) ≤ stT294 182 := by
  have hc : ((-249129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147733497/2000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-249129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c183 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-89/2000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4038277/10000000) (δ := 14753/1000000000) (ψ := 6689/62500) 294 244
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t183 : ((-82423253/25000000000 : ℚ) : ℝ) ≤ stT294 183 := by
  have hc : ((-223/5000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82423253/25000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-223/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c184 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((499957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32821/10000000) (δ := 14753/1000000000) (ψ := 6689/62500) 294 244
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t184 : ((368535939563/5000000000000 : ℚ) : ℝ) ≤ stT294 184 := by
  have hc : ((499907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368535939563/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((499907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c185 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-599/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 493869/1250000) (δ := 297/20000000) (ψ := 6689/62500) 294 244
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t185 : ((-355991103/500000000000 : ℚ) : ℝ) ≤ stT294 185 := by
  have hc : ((-2421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355991103/500000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-2421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c186 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-24993/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7794773/10000000) (δ := 14743/1000000000) (ψ := 6689/62500) 294 245
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t186 : ((-9163800219/125000000000 : ℚ) : ℝ) ≤ stT294 186 := by
  have hc : ((-49991/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9163800219/125000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-49991/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c187 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((29311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3853703/10000000) (δ := 14743/1000000000) (ψ := 6689/62500) 294 245
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t187 : ((2670148299/1250000000000 : ℚ) : ℝ) ≤ stT294 187 := by
  have hc : ((29211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2670148299/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((29211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c188 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((999649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66273/10000000) (δ := 743/50000000) (ψ := 6689/62500) 294 245
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t188 : ((182248768719/2500000000000 : ℚ) : ℝ) ≤ stT294 188 := by
  have hc : ((999549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182248768719/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((999549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c189 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-15411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3965521/10000000) (δ := 14743/1000000000) (ψ := 6689/62500) 294 245
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t189 : ((-11282592823/10000000000000 : ℚ) : ℝ) ≤ stT294 189 := by
  have hc : ((-15511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11282592823/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-15511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c190 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-124999/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1961029/2500000) (δ := 14743/1000000000) (ψ := 6689/62500) 294 245
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t190 : ((-181385935971/2500000000000 : ℚ) : ℝ) ≤ stT294 190 := by
  have hc : ((-250023/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181385935971/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-250023/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c191 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-15707/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2002769/5000000) (δ := 923/62500000) (ψ := 6689/62500) 294 246
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t191 : ((-456054851/200000000000 : ℚ) : ℝ) ≤ stT294 191 := by
  have hc : ((-15757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-456054851/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-15757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c192 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((498879/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83721/5000000) (δ := 2967/200000000) (ψ := 6689/62500) 294 246
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t192 : ((359998404523/5000000000000 : ℚ) : ℝ) ≤ stT294 192 := by
  have hc : ((498829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((359998404523/5000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((498829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c193 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((110277/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228171/625000) (δ := 2967/200000000) (ψ := 6689/62500) 294 246
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t193 : ((15861411451/2000000000000 : ℚ) : ℝ) ≤ stT294 193 := by
  have hc : ((110177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15861411451/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((110177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c194 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-493461/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58197/78125) (δ := 2967/200000000) (ψ := 6689/62500) 294 246
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t194 : ((-354320664049/5000000000000 : ℚ) : ℝ) ≤ stT294 194 := by
  have hc : ((-493511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354320664049/5000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-493511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c195 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-219333/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2239909/5000000) (δ := 1841/125000000) (ψ := 6689/62500) 294 247
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t195 : ((-31427852559/2000000000000 : ℚ) : ℝ) ≤ stT294 195 := by
  have hc : ((-219433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31427852559/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-219433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c196 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((958789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -720219/10000000) (δ := 119/8000000) (ψ := 6689/62500) 294 247
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t196 : ((136955434473/2000000000000 : ℚ) : ℝ) ≤ stT294 196 := by
  have hc : ((958689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136955434473/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((958689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c197 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((354789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3020269/10000000) (δ := 1841/125000000) (ψ := 6689/62500) 294 247
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t197 : ((25270527183/1000000000000 : ℚ) : ℝ) ≤ stT294 197 := by
  have hc : ((354689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25270527183/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((354689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c198 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-180533/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1348359/2000000) (δ := 119/8000000) (ψ := 6689/62500) 294 247
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t198 : ((-12831360051/200000000000 : ℚ) : ℝ) ≤ stT294 198 := by
  have hc : ((-180553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12831360051/200000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-180553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c199 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-509461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2631693/5000000) (δ := 14821/1000000000) (ψ := 6689/62500) 294 248
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t199 : ((-180609310401/5000000000000 : ℚ) : ℝ) ≤ stT294 199 := by
  have hc : ((-509561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180609310401/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-509561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c200 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((807037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789599/5000000) (δ := 7391/500000000) (ψ := 6689/62500) 294 248
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t200 : ((285294997161/5000000000000 : ℚ) : ℝ) ≤ stT294 200 := by
  have hc : ((806937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285294997161/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((806937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c201 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((335709/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65209/312500) (δ := 7391/500000000) (ψ := 6689/62500) 294 248
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t201 : ((47351079471/1000000000000 : ℚ) : ℝ) ≤ stT294 201 := by
  have hc : ((335659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47351079471/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((335659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c202 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-661571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44799/78125) (δ := 14821/1000000000) (ψ := 6689/62500) 294 248
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t202 : ((-232775196129/5000000000000 : ℚ) : ℝ) ≤ stT294 202 := by
  have hc : ((-661671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232775196129/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-661671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c203 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-205771/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158601/250000) (δ := 14889/1000000000) (ψ := 6689/62500) 294 249
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t203 : ((-36110149487/625000000000 : ℚ) : ℝ) ≤ stT294 203 := by
  have hc : ((-51449/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36110149487/625000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-51449/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c204 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((57489/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10929/40000) (δ := 14889/1000000000) (ψ := 6689/62500) 294 249
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t204 : ((4024159671/125000000000 : ℚ) : ℝ) ≤ stT294 204 := by
  have hc : ((114953/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4024159671/125000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((114953/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c205 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((941157/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8619/100000) (δ := 14889/1000000000) (ψ := 6689/62500) 294 249
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t205 : ((65726244051/1000000000000 : ℚ) : ℝ) ≤ stT294 205 := by
  have hc : ((941057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65726244051/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((941057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c206 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-203201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4438557/10000000) (δ := 14889/1000000000) (ψ := 6689/62500) 294 249
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t206 : ((-70823359467/5000000000000 : ℚ) : ℝ) ≤ stT294 206 := by
  have hc : ((-203301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70823359467/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-203301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c207 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-124793/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -481881/625000) (δ := 14807/1000000000) (ψ := 6689/62500) 294 250
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t207 : ((-173491875939/2500000000000 : ℚ) : ℝ) ≤ stT294 207 := by
  have hc : ((-249611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173491875939/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-249611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c208 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-96219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -416791/1000000) (δ := 3699/250000000) (ψ := 6689/62500) 294 250
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t208 : ((-521760023/78125000000 : ℚ) : ℝ) ≤ stT294 208 := by
  have hc : ((-96319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521760023/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-96319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c209 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((30223/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -642703/10000000) (δ := 3699/250000000) (ψ := 6689/62500) 294 250
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t209 : ((83614042463/1250000000000 : ℚ) : ℝ) ≤ stT294 209 := by
  have hc : ((241759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83614042463/1250000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((241759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c210 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((41189/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 358209/1250000) (δ := 14807/1000000000) (ψ := 6689/62500) 294 250
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t210 : ((5683237327/200000000000 : ℚ) : ℝ) ≤ stT294 210 := by
  have hc : ((41179/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5683237327/200000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((41179/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c211 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-826099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6357363/10000000) (δ := 14807/1000000000) (ψ := 6689/62500) 294 250
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t211 : ((-568779351371/10000000000000 : ℚ) : ℝ) ≤ stT294 211 := by
  have hc : ((-826199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568779351371/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-826199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c212 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-17571/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5875447/10000000) (δ := 14899/1000000000) (ψ := 6689/62500) 294 251
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t212 : ((-24139065041/500000000000 : ℚ) : ℝ) ≤ stT294 212 := by
  have hc : ((-35147/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24139065041/500000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-35147/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c213 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((113613/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241661/1000000) (δ := 919/62500000) (ψ := 6689/62500) 294 251
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t213 : ((19458140121/500000000000 : ℚ) : ℝ) ≤ stT294 213 := by
  have hc : ((113593/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19458140121/500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((113593/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c214 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((114619/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128257/1250000) (δ := 14899/1000000000) (ψ := 6689/62500) 294 251
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t214 : ((31337313721/500000000000 : ℚ) : ℝ) ≤ stT294 214 := by
  have hc : ((229213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31337313721/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((229213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c215 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-52177/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2226313/5000000) (δ := 14899/1000000000) (ψ := 6689/62500) 294 251
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t215 : ((-3560150299/250000000000 : ℚ) : ℝ) ≤ stT294 215 := by
  have hc : ((-26101/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3560150299/250000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-26101/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c216 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-999993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7844643/10000000) (δ := 1849/125000000) (ψ := 6689/62500) 294 252
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t216 : ((-340238639251/5000000000000 : ℚ) : ℝ) ≤ stT294 216 := by
  have hc : ((-1000093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340238639251/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-1000093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c217 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-6487/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4449751/10000000) (δ := 14811/1000000000) (ψ := 6689/62500) 294 252
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t217 : ((-7049262249/500000000000 : ℚ) : ℝ) ≤ stT294 217 := by
  have hc : ((-51921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7049262249/500000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-51921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c218 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((227431/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -535221/5000000) (δ := 1849/125000000) (ψ := 6689/62500) 294 252
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t218 : ((15401867271/250000000000 : ℚ) : ℝ) ≤ stT294 218 := by
  have hc : ((113703/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15401867271/250000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((113703/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c219 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((151977/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2293433/10000000) (δ := 14811/1000000000) (ψ := 6689/62500) 294 252
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t219 : ((6417474289/156250000000 : ℚ) : ℝ) ≤ stT294 219 := by
  have hc : ((9497/15625 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6417474289/156250000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((9497/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c220 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-633433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2820973/5000000) (δ := 14811/1000000000) (ψ := 6689/62500) 294 252
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t220 : ((-2135639743/50000000000 : ℚ) : ℝ) ≤ stT294 220 := by
  have hc : ((-633533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2135639743/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-633533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c221 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-225271/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3366323/5000000) (δ := 2977/200000000) (ψ := 6689/62500) 294 253
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t221 : ((-9471908513/156250000000 : ℚ) : ℝ) ≤ stT294 221 := by
  have hc : ((-14081/15625 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9471908513/156250000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-14081/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c222 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((203597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -682883/2000000) (δ := 2977/200000000) (ψ := 6689/62500) 294 253
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t222 : ((34144558133/2500000000000 : ℚ) : ℝ) ≤ stT294 222 := by
  have hc : ((203497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34144558133/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((203497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c223 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((499507/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111031/10000000) (δ := 2977/200000000) (ψ := 6689/62500) 294 253
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t223 : ((334460880593/5000000000000 : ℚ) : ℝ) ≤ stT294 223 := by
  have hc : ((499457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334460880593/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((499457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c224 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((59059/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158879/500000) (δ := 7359/500000000) (ψ := 6689/62500) 294 253
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t224 : ((39447084967/2000000000000 : ℚ) : ℝ) ≤ stT294 224 := by
  have hc : ((59039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39447084967/2000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((59039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c225 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-846741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1612891/2500000) (δ := 7359/500000000) (ψ := 6689/62500) 294 253
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t225 : ((-564560948947/10000000000000 : ℚ) : ℝ) ≤ stT294 225 := by
  have hc : ((-846841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564560948947/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-846841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c226 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-92073/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1199401/2000000) (δ := 1177/40000000) (ψ := 6689/62500) 294 254
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t226 : ((-122508891661/2500000000000 : ℚ) : ℝ) ≤ stT294 226 := by
  have hc : ((-184171/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122508891661/2500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-184171/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c227 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((452903/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2751943/10000000) (δ := 593/40000000) (ψ := 6689/62500) 294 254
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t227 : ((300535765569/10000000000000 : ℚ) : ℝ) ≤ stT294 227 := by
  have hc : ((452803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300535765569/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((452803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c228 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((490857/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 478823/10000000) (δ := 593/40000000) (ψ := 6689/62500) 294 254
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t228 : ((162522394331/2500000000000 : ℚ) : ℝ) ≤ stT294 228 := by
  have hc : ((490807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162522394331/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((490807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c229 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((92473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3695477/10000000) (δ := 593/40000000) (ψ := 6689/62500) 294 254
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t229 : ((30520870557/5000000000000 : ℚ) : ℝ) ≤ stT294 229 := by
  have hc : ((92373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30520870557/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((92373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c230 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-231947/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1724523/2500000) (δ := 7389/500000000) (ψ := 6689/62500) 294 254
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t230 : ((-38239482333/625000000000 : ℚ) : ℝ) ≤ stT294 230 := by
  have hc : ((-57993/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38239482333/625000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-57993/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c231 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-313487/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5621147/10000000) (δ := 3683/250000000) (ψ := 6689/62500) 294 255
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t231 : ((-6446634257/156250000000 : ℚ) : ℝ) ≤ stT294 231 := by
  have hc : ((-313537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6446634257/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-313537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c232 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((558271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2446241/10000000) (δ := 3683/250000000) (ψ := 6689/62500) 294 255
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t232 : ((91614280743/2500000000000 : ℚ) : ℝ) ≤ stT294 232 := by
  have hc : ((558171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91614280743/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((558171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c233 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((239843/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715067/10000000) (δ := 14871/1000000000) (ψ := 6689/62500) 294 255
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t233 : ((78554903989/1250000000000 : ℚ) : ℝ) ≤ stT294 233 := by
  have hc : ((119909/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78554903989/1250000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((119909/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c234 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((25653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 965713/2500000) (δ := 3683/250000000) (ψ := 6689/62500) 294 255
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t234 : ((417612679/250000000000 : ℚ) : ℝ) ≤ stT294 234 := by
  have hc : ((25553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417612679/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((25553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c235 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-188369/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3498593/5000000) (δ := 3683/250000000) (ψ := 6689/62500) 294 255
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t235 : ((-122891607981/2000000000000 : ℚ) : ℝ) ≤ stT294 235 := by
  have hc : ((-188389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122891607981/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-188389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c236 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-30857/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5589747/10000000) (δ := 3691/250000000) (ψ := 6689/62500) 294 256
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t236 : ((-2008946459/50000000000 : ℚ) : ℝ) ≤ stT294 236 := by
  have hc : ((-15431/25000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2008946459/50000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-15431/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c237 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((109273/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1240973/5000000) (δ := 14839/1000000000) (ψ := 6689/62500) 294 256
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t237 : ((70967361957/2000000000000 : ℚ) : ℝ) ≤ stT294 237 := by
  have hc : ((109253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70967361957/2000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((109253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c238 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((970111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 612771/10000000) (δ := 3691/250000000) (ψ := 6689/62500) 294 256
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t238 : ((628764040233/10000000000000 : ℚ) : ℝ) ≤ stT294 238 := by
  have hc : ((970011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((628764040233/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((970011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c239 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((92841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3694553/10000000) (δ := 14839/1000000000) (ψ := 6689/62500) 294 256
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t239 : ((29994572443/5000000000000 : ℚ) : ℝ) ≤ stT294 239 := by
  have hc : ((92741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29994572443/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((92741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c240 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-453181/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 422717/625000) (δ := 14839/1000000000) (ψ := 6689/62500) 294 256
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t240 : ((-146279852019/2500000000000 : ℚ) : ℝ) ≤ stT294 240 := by
  have hc : ((-453231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146279852019/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-453231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c241 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-353253/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2944181/5000000) (δ := 1857/125000000) (ψ := 6689/62500) 294 257
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t241 : ((-227582600571/5000000000000 : ℚ) : ℝ) ≤ stT294 241 := by
  have hc : ((-353303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227582600571/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-353303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c242 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((419457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1422437/5000000) (δ := 1857/125000000) (ψ := 6689/62500) 294 257
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t242 : ((33696593021/1250000000000 : ℚ) : ℝ) ≤ stT294 242 := by
  have hc : ((419357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33696593021/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((419357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c243 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((62327/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93023/5000000) (δ := 14747/1000000000) (ψ := 6689/62500) 294 257
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t243 : ((319830089/5000000000 : ℚ) : ℝ) ≤ stT294 243 := by
  have hc : ((249283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319830089/5000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((249283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c244 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((284973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50071/156250) (δ := 14747/1000000000) (ψ := 6689/62500) 294 257
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t244 : ((22796392079/1250000000000 : ℚ) : ℝ) ≤ stT294 244 := by
  have hc : ((284873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22796392079/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((284873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c245 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-791627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6210657/10000000) (δ := 1841/62500000) (ψ := 6689/62500) 294 257
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t245 : ((-505816170579/10000000000000 : ℚ) : ℝ) ≤ stT294 245 := by
  have hc : ((-791727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505816170579/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-791727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c246 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-214397/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3251697/5000000) (δ := 14749/1000000000) (ψ := 6689/62500) 294 258
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t246 : ((-68355267747/1250000000000 : ℚ) : ℝ) ≤ stT294 246 := by
  have hc : ((-107211/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68355267747/1250000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-107211/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c247 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((40357/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760823/5000000) (δ := 14749/1000000000) (ψ := 6689/62500) 294 258
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t247 : ((1603912893/156250000000 : ℚ) : ℝ) ≤ stT294 247 := by
  have hc : ((10083/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1603912893/156250000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((10083/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c248 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((975727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34497/625000) (δ := 14749/1000000000) (ψ := 6689/62500) 294 258
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t248 : ((123904629/2000000000 : ℚ) : ℝ) ≤ stT294 248 := by
  have hc : ((975627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123904629/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((975627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c249 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((57163/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1202881/5000000) (δ := 7427/500000000) (ψ := 6689/62500) 294 258
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t249 : ((9054806943/250000000000 : ℚ) : ℝ) ≤ stT294 249 := by
  have hc : ((57153/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9054806943/250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((57153/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c250 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-539539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1070343/2000000) (δ := 14749/1000000000) (ψ := 6689/62500) 294 258
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t250 : ((-42662240423/1250000000000 : ℚ) : ℝ) ≤ stT294 250 := by
  have hc : ((-539639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42662240423/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-539639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c251 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-985117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -463883/625000) (δ := 14761/1000000000) (ψ := 6689/62500) 294 259
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t251 : ((-124372808863/2000000000000 : ℚ) : ℝ) ≤ stT294 251 := by
  have hc : ((-985217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124372808863/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-985217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c252 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-227083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -899939/2000000) (δ := 7421/500000000) (ψ := 6689/62500) 294 259
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t252 : ((-143111886203/10000000000000 : ℚ) : ℝ) ≤ stT294 252 := by
  have hc : ((-227183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143111886203/10000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-227183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c253 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((804763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1588801/10000000) (δ := 7421/500000000) (ψ := 6689/62500) 294 259
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t253 : ((252943400061/5000000000000 : ℚ) : ℝ) ≤ stT294 253 := by
  have hc : ((804663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252943400061/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((804663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c254 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((865699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1310627/10000000) (δ := 7421/500000000) (ψ := 6689/62500) 294 259
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t254 : ((108624884109/2000000000000 : ℚ) : ℝ) ≤ stT294 254 := by
  have hc : ((865599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108624884109/2000000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((865599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c255 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-21691/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4198663/10000000) (δ := 14761/1000000000) (ψ := 6689/62500) 294 259
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t255 : ((-543838839/80000000000 : ℚ) : ℝ) ≤ stT294 255 := by
  have hc : ((-21711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543838839/80000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-21711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c256 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-951893/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7075379/10000000) (δ := 7421/500000000) (ψ := 6689/62500) 294 259
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t256 : ((-594996576993/10000000000000 : ℚ) : ℝ) ≤ stT294 256 := by
  have hc : ((-951993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-594996576993/10000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-951993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c257 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-134273/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5767113/10000000) (δ := 2947/200000000) (ψ := 6689/62500) 294 260
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t257 : ((-83769690419/2000000000000 : ℚ) : ℝ) ≤ stT294 257 := by
  have hc : ((-134293/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83769690419/2000000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-134293/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c258 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((197331/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145637/500000) (δ := 3717/250000000) (ψ := 6689/62500) 294 260
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t258 : ((30705406683/1250000000000 : ℚ) : ℝ) ≤ stT294 258 := by
  have hc : ((197281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30705406683/1250000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((197281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c259 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((199923/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69393/10000000) (δ := 2947/200000000) (ψ := 6689/62500) 294 260
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t259 : ((124213527207/2000000000000 : ℚ) : ℝ) ≤ stT294 259 := by
  have hc : ((199903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124213527207/2000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((199903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c260 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((89791/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2763003/10000000) (δ := 2947/200000000) (ψ := 6689/62500) 294 260
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t260 : ((55673550383/2000000000000 : ℚ) : ℝ) ≤ stT294 260 := by
  have hc : ((89771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55673550383/2000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((89771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c261 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-307747/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5584521/10000000) (δ := 2947/200000000) (ψ := 6689/62500) 294 260
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t261 : ((-38104345209/1000000000000 : ℚ) : ℝ) ≤ stT294 261 := by
  have hc : ((-307797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38104345209/1000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-307797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c262 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-195331/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7312729/10000000) (δ := 11057/250000000) (ψ := 6689/62500) 294 261
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t262 : ((-120688433853/2000000000000 : ℚ) : ℝ) ≤ stT294 262 := by
  have hc : ((-195351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120688433853/2000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-195351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c263 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-58041/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2256373/5000000) (δ := 591/40000000) (ψ := 6689/62500) 294 261
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t263 : ((-17902531691/1250000000000 : ℚ) : ℝ) ≤ stT294 263 := by
  have hc : ((-29033/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17902531691/1250000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-29033/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c264 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((385833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430837/2500000) (δ := 11057/250000000) (ψ := 6689/62500) 294 261
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t264 : ((237432847831/5000000000000 : ℚ) : ℝ) ≤ stT294 264 := by
  have hc : ((385783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237432847831/5000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((385783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c265 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((182439/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1055467/10000000) (δ := 591/40000000) (ψ := 6689/62500) 294 261
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t265 : ((22411815921/400000000000 : ℚ) : ℝ) ≤ stT294 265 := by
  have hc : ((182419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22411815921/400000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((182419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c266 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((41247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955961/2500000) (δ := 3707/250000000) (ψ := 6689/62500) 294 261
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t266 : ((25228830433/10000000000000 : ℚ) : ℝ) ≤ stT294 266 := by
  have hc : ((41147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25228830433/10000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((41147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c267 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-873291/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316357/2000000) (δ := 591/40000000) (ψ := 6689/62500) 294 261
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t267 : ((-534507431481/10000000000000 : ℚ) : ℝ) ≤ stT294 267 := by
  have hc : ((-873391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534507431481/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-873391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c268 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-20771/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199329/312500) (δ := 23/1562500) (ψ := 6689/62500) 294 262
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t268 : ((-793090683/15625000000 : ℚ) : ℝ) ≤ stT294 268 := by
  have hc : ((-41547/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-793090683/15625000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-41547/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c269 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((11411/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1820547/5000000) (δ := 23/1562500) (ψ := 6689/62500) 294 262
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t269 : ((695130371/100000000000 : ℚ) : ℝ) ≤ stT294 269 := by
  have hc : ((11401/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((695130371/100000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((11401/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c270 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((466969/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -913803/10000000) (δ := 23/1562500) (ψ := 6689/62500) 294 262
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t270 : ((14207878251/250000000000 : ℚ) : ℝ) ≤ stT294 270 := by
  have hc : ((466919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14207878251/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((466919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c271 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((750903/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1803419/10000000) (δ := 14883/1000000000) (ψ := 6689/62500) 294 262
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t271 : ((14252493349/312500000000 : ℚ) : ℝ) ≤ stT294 271 := by
  have hc : ((750803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14252493349/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((750803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c272 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-115659/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4510571/10000000) (δ := 14883/1000000000) (ψ := 6689/62500) 294 262
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t272 : ((-3507949753/250000000000 : ℚ) : ℝ) ≤ stT294 272 := by
  have hc : ((-115709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3507949753/250000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-115709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c273 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-483391/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36039/50000) (δ := 23/1562500) (ψ := 6689/62500) 294 262
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t273 : ((-73148007387/1250000000000 : ℚ) : ℝ) ≤ stT294 273 := by
  have hc : ((-483441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73148007387/1250000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-483441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c274 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-684769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5812709/10000000) (δ := 1479/100000000) (ψ := 6689/62500) 294 263
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t274 : ((-413745114887/10000000000000 : ℚ) : ℝ) ≤ stT294 274 := by
  have hc : ((-684869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-413745114887/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-684869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c275 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((9733/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1567589/5000000) (δ := 14813/1000000000) (ψ := 6689/62500) 294 263
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t275 : ((23469314729/1250000000000 : ℚ) : ℝ) ≤ stT294 275 := by
  have hc : ((77839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23469314729/1250000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((77839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c276 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((982583/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18691/400000) (δ := 14813/1000000000) (ψ := 6689/62500) 294 263
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t276 : ((591385009707/10000000000000 : ℚ) : ℝ) ≤ stT294 276 := by
  have hc : ((982483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((591385009707/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((982483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c277 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((319961/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2191/10000) (δ := 1479/100000000) (ψ := 6689/62500) 294 263
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t277 : ((192215645151/5000000000000 : ℚ) : ℝ) ≤ stT294 277 := by
  have hc : ((319911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192215645151/5000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((319911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c278 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-357007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2419823/5000000) (δ := 1479/100000000) (ψ := 6689/62500) 294 263
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t278 : ((-214178851427/10000000000000 : ℚ) : ℝ) ≤ stT294 278 := by
  have hc : ((-357107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214178851427/10000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-357107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c279 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-247189/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7478737/10000000) (δ := 1479/100000000) (ψ := 6689/62500) 294 263
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t279 : ((-14800331359/250000000000 : ℚ) : ℝ) ≤ stT294 279 := by
  have hc : ((-123607/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14800331359/250000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-123607/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c280 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-124039/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -559947/1000000) (δ := 7353/500000000) (ψ := 6689/62500) 294 264
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t280 : ((-14827903857/400000000000 : ℚ) : ℝ) ≤ stT294 280 := by
  have hc : ((-124059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14827903857/400000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-124059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c281 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((185051/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595839/2000000) (δ := 7353/500000000) (ψ := 6689/62500) 294 264
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t281 : ((110362161549/5000000000000 : ℚ) : ℝ) ≤ stT294 281 := by
  have hc : ((185001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110362161549/5000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((185001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c282 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((39567/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368181/10000000) (δ := 7353/500000000) (ψ := 6689/62500) 294 264
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t282 : ((23559410433/400000000000 : ℚ) : ℝ) ≤ stT294 282 := by
  have hc : ((39563/40000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23559410433/400000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((39563/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c283 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((78343/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 558393/2500000) (δ := 7353/500000000) (ψ := 6689/62500) 294 264
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t283 : ((46562625759/1250000000000 : ℚ) : ℝ) ≤ stT294 283 := by
  have hc : ((156661/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46562625759/1250000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((156661/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c284 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-175991/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4826211/10000000) (δ := 7353/500000000) (ψ := 6689/62500) 294 264
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t284 : ((-104461145031/5000000000000 : ℚ) : ℝ) ≤ stT294 284 := by
  have hc : ((-176041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104461145031/5000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-176041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c285 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-123031/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7409663/10000000) (δ := 14897/1000000000) (ψ := 6689/62500) 294 264
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t285 : ((-145769388363/2500000000000 : ℚ) : ℝ) ≤ stT294 285 := by
  have hc : ((-246087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145769388363/2500000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-246087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c286 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-658429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -715477/1250000) (δ := 3701/250000000) (ψ := 6689/62500) 294 265
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t286 : ((-389396758577/10000000000000 : ℚ) : ℝ) ≤ stT294 286 := by
  have hc : ((-658529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389396758577/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-658529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c287 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((302627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789593/2500000) (δ := 3701/250000000) (ψ := 6689/62500) 294 265
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t287 : ((178575940087/10000000000000 : ℚ) : ℝ) ≤ stT294 287 := by
  have hc : ((302527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178575940087/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((302527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c288 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((485579/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120379/2000000) (δ := 3701/250000000) (ψ := 6689/62500) 294 265
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t288 : ((57220078179/1000000000000 : ℚ) : ℝ) ≤ stT294 288 := by
  have hc : ((485529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57220078179/1000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((485529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c289 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((142421/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 972881/5000000) (δ := 3701/250000000) (ψ := 6689/62500) 294 265
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t289 : ((16753050447/400000000000 : ℚ) : ℝ) ≤ stT294 289 := by
  have hc : ((142401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16753050447/400000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((142401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c290 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-221227/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70073/156250) (δ := 14799/1000000000) (ψ := 6689/62500) 294 265
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t290 : ((-129967862267/10000000000000 : ℚ) : ℝ) ≤ stT294 290 := by
  have hc : ((-221327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129967862267/10000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-221327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c291 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-118023/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7014763/10000000) (δ := 3701/250000000) (ψ := 6689/62500) 294 265
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t291 : ((-138387416981/2500000000000 : ℚ) : ℝ) ≤ stT294 291 := by
  have hc : ((-236071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138387416981/2500000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-236071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c292 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-195503/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -617171/1000000) (δ := 3723/250000000) (ψ := 6689/62500) 294 266
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t292 : ((-7151509923/156250000000 : ℚ) : ℝ) ≤ stT294 292 := by
  have hc : ((-24441/31250 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7151509923/156250000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-24441/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c293 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((53517/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -914723/2500000) (δ := 3723/250000000) (ψ := 6689/62500) 294 266
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t293 : ((15617871101/2500000000000 : ℚ) : ℝ) ≤ stT294 293 := by
  have hc : ((53467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15617871101/2500000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((53467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c294 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((895221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1154673/10000000) (δ := 14711/1000000000) (ψ := 6689/62500) 294 266
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t294 : ((522044413531/10000000000000 : ℚ) : ℝ) ≤ stT294 294 := by
  have hc : ((895121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((522044413531/10000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((895121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c295 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((171907/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1341093/10000000) (δ := 14711/1000000000) (ψ := 6689/62500) 294 266
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t295 : ((50038196457/1000000000000 : ℚ) : ℝ) ≤ stT294 295 := by
  have hc : ((171887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50038196457/1000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((171887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c296 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((616/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1914203/5000000) (δ := 3723/250000000) (ψ := 6689/62500) 294 266
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t296 : ((2857075389/1250000000000 : ℚ) : ℝ) ≤ stT294 296 := by
  have hc : ((9831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2857075389/1250000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((9831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c297 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-407329/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6307341/10000000) (δ := 14711/1000000000) (ψ := 6689/62500) 294 266
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t297 : ((-236385331161/5000000000000 : ℚ) : ℝ) ≤ stT294 297 := by
  have hc : ((-407379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236385331161/5000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-407379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c298 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-233121/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6930067/10000000) (δ := 2957/200000000) (ψ := 6689/62500) 294 267
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t298 : ((-13505798061/250000000000 : ℚ) : ℝ) ≤ stT294 298 := by
  have hc : ((-116573/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13505798061/250000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-116573/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c299 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-107309/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4467743/10000000) (δ := 7409/500000000) (ψ := 6689/62500) 294 267
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t299 : ((-12417464017/1000000000000 : ℚ) : ℝ) ≤ stT294 299 := by
  have hc : ((-107359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12417464017/1000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-107359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c300 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((692779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503413/2500000) (δ := 2957/200000000) (ψ := 6689/62500) 294 267
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t300 : ((7998364413/200000000000 : ℚ) : ℝ) ≤ stT294 300 := by
  have hc : ((692679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7998364413/200000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((692679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c301 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((15392/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432281/10000000) (δ := 2957/200000000) (ψ := 6689/62500) 294 267
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t301 : ((14193430833/250000000000 : ℚ) : ℝ) ≤ stT294 301 := by
  have hc : ((246247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14193430833/250000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((246247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c302 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((82053/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2870129/10000000) (δ := 2957/200000000) (ψ := 6689/62500) 294 267
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t302 : ((9440931871/400000000000 : ℚ) : ℝ) ≤ stT294 302 := by
  have hc : ((82033/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9440931871/400000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((82033/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c303 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-521971/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1324973/2500000) (δ := 2957/200000000) (ψ := 6689/62500) 294 267
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t303 : ((-59984391687/2000000000000 : ℚ) : ℝ) ≤ stT294 303 := by
  have hc : ((-522071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59984391687/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-522071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c304 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-998599/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1930411/2500000) (δ := 7409/500000000) (ψ := 6689/62500) 294 267
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t304 : ((-28639691223/500000000000 : ℚ) : ℝ) ≤ stT294 304 := by
  have hc : ((-998699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28639691223/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-998699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c305 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-305861/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278629/500000) (δ := 14877/1000000000) (ψ := 6689/62500) 294 268
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t305 : ((-175164332689/5000000000000 : ℚ) : ℝ) ≤ stT294 305 := by
  have hc : ((-305911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175164332689/5000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-305911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c306 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((299477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3166631/10000000) (δ := 14877/1000000000) (ψ := 6689/62500) 294 268
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t306 : ((171142155197/10000000000000 : ℚ) : ℝ) ≤ stT294 306 := by
  have hc : ((299377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171142155197/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((299377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c307 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((953109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38431/500000) (δ := 14877/1000000000) (ψ := 6689/62500) 294 268
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t307 : ((54391082657/1000000000000 : ℚ) : ℝ) ≤ stT294 307 := by
  have hc : ((953009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54391082657/1000000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((953009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c308 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((398453/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2027/12500) (δ := 14877/1000000000) (ψ := 6689/62500) 294 268
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t308 : ((113505413103/2500000000000 : ℚ) : ℝ) ≤ stT294 308 := by
  have hc : ((398403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113505413103/2500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((398403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c309 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-771/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4004103/10000000) (δ := 7363/500000000) (ψ := 6689/62500) 294 268
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t309 : ((-880058907/500000000000 : ℚ) : ℝ) ≤ stT294 309 := by
  have hc : ((-1547/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-880058907/500000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-1547/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c310 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-20773/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 797361/1250000) (δ := 7363/500000000) (ψ := 6689/62500) 294 268
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t310 : ((-11799694531/250000000000 : ℚ) : ℝ) ≤ stT294 310 := by
  have hc : ((-41551/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11799694531/250000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-41551/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c311 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-468501/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6961861/10000000) (δ := 1477/100000000) (ψ := 6689/62500) 294 269
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t311 : ((-33211363431/625000000000 : ℚ) : ℝ) ≤ stT294 311 := by
  have hc : ((-468551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33211363431/625000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-468551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c312 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-427/1600 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1150591/2500000) (δ := 1477/100000000) (ψ := 6689/62500) 294 269
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t312 : ((-6045798381/400000000000 : ℚ) : ℝ) ≤ stT294 312 := by
  have hc : ((-10679/40000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6045798381/400000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-10679/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c313 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((77687/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -562591/2500000) (δ := 1477/100000000) (ψ := 6689/62500) 294 269
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t313 : ((87808381317/2500000000000 : ℚ) : ℝ) ≤ stT294 313 := by
  have hc : ((155349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87808381317/2500000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((155349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c314 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((999291/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94139/10000000) (δ := 1477/100000000) (ψ := 6689/62500) 294 269
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t314 : ((140968863853/2500000000000 : ℚ) : ℝ) ≤ stT294 314 := by
  have hc : ((999191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140968863853/2500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((999191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c315 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((281623/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2431219/10000000) (δ := 14833/1000000000) (ψ := 6689/62500) 294 269
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t315 : ((39662091207/1250000000000 : ℚ) : ℝ) ≤ stT294 315 := by
  have hc : ((281573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39662091207/1250000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((281573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c316 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-327403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38087/80000) (δ := 14833/1000000000) (ψ := 6689/62500) 294 269
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t316 : ((-11514677977/625000000000 : ℚ) : ℝ) ≤ stT294 316 := by
  have hc : ((-327503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11514677977/625000000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-327503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c317 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-238209/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7083107/10000000) (δ := 1477/100000000) (ψ := 6689/62500) 294 269
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t317 : ((-8362847219/156250000000 : ℚ) : ℝ) ≤ stT294 317 := by
  have hc : ((-119117/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8362847219/156250000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-119117/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c318 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-203813/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63099/100000) (δ := 737/50000000) (ψ := 6689/62500) 294 270
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t318 : ((-57153423387/1250000000000 : ℚ) : ℝ) ≤ stT294 318 := by
  have hc : ((-101919/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57153423387/1250000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-101919/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c319 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-15029/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4002147/10000000) (δ := 737/50000000) (ψ := 6689/62500) 294 270
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t319 : ((-8442626547/5000000000000 : ℚ) : ℝ) ≤ stT294 319 := by
  have hc : ((-15079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8442626547/5000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-15079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c320 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((388567/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106359/625000) (δ := 737/50000000) (ψ := 6689/62500) 294 270
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t320 : ((27148402409/625000000000 : ℚ) : ℝ) ≤ stT294 320 := by
  have hc : ((388517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27148402409/625000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((388517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c321 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((972131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591603/10000000) (δ := 737/50000000) (ψ := 6689/62500) 294 270
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t321 : ((108506848499/2000000000000 : ℚ) : ℝ) ≤ stT294 321 := by
  have hc : ((972031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108506848499/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((972031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c322 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((101871/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2877747/10000000) (δ := 737/50000000) (ψ := 6689/62500) 294 270
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t322 : ((14189133797/625000000000 : ℚ) : ℝ) ≤ stT294 322 := by
  have hc : ((50923/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14189133797/625000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((50923/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c323 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-94467/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1031367/2000000) (δ := 737/50000000) (ψ := 6689/62500) 294 270
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t323 : ((-10514796821/400000000000 : ℚ) : ℝ) ≤ stT294 323 := by
  have hc : ((-94487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10514796821/400000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-94487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c324 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-985577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7428867/10000000) (δ := 737/50000000) (ψ := 6689/62500) 294 270
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t324 : ((-136899692853/2500000000000 : ℚ) : ℝ) ≤ stT294 324 := by
  have hc : ((-985677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136899692853/2500000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-985677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c325 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-741197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150353/250000) (δ := 14847/1000000000) (ψ := 6689/62500) 294 271
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t325 : ((-411198187197/10000000000000 : ℚ) : ℝ) ≤ stT294 325 := by
  have hc : ((-741297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411198187197/10000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-741297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c326 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((34161/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3756053/10000000) (δ := 14847/1000000000) (ψ := 6689/62500) 294 271
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t326 : ((2361538641/625000000000 : ℚ) : ℝ) ≤ stT294 326 := by
  have hc : ((34111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2361538641/625000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((34111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c327 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((206057/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -300979/2000000) (δ := 14847/1000000000) (ψ := 6689/62500) 294 271
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t327 : ((7120993877/156250000000 : ℚ) : ℝ) ≤ stT294 327 := by
  have hc : ((12877/15625 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7120993877/156250000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((12877/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c328 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((478289/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 739427/10000000) (δ := 3689/250000000) (ψ := 6689/62500) 294 271
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t328 : ((264063011523/5000000000000 : ℚ) : ℝ) ≤ stT294 328 := by
  have hc : ((478239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264063011523/5000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((478239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c329 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((11593/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2976841/10000000) (δ := 14847/1000000000) (ψ := 6689/62500) 294 271
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t329 : ((51117560923/2500000000000 : ℚ) : ℝ) ≤ stT294 329 := by
  have hc : ((92719/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51117560923/2500000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((92719/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c330 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-490097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1301873/2500000) (δ := 3689/250000000) (ψ := 6689/62500) 294 271
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t330 : ((-134922312477/5000000000000 : ℚ) : ℝ) ≤ stT294 330 := by
  have hc : ((-490197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134922312477/5000000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-490197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c331 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-985747/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3715691/5000000) (δ := 14847/1000000000) (ψ := 6689/62500) 294 271
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t331 : ((-10837416071/200000000000 : ℚ) : ℝ) ≤ stT294 331 := by
  have hc : ((-985847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10837416071/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-985847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c332 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-188307/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6059381/10000000) (δ := 14849/1000000000) (ψ := 6689/62500) 294 272
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t332 : ((-12920093113/312500000000 : ℚ) : ℝ) ≤ stT294 332 := by
  have hc : ((-47083/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12920093113/312500000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-47083/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c333 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((7811/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962217/2500000) (δ := 7377/500000000) (ψ := 6689/62500) 294 272
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t333 : ((533337107/312500000000 : ℚ) : ℝ) ≤ stT294 333 := by
  have hc : ((3893/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((533337107/312500000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((3893/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c334 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((98903/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1644971/10000000) (δ := 14849/1000000000) (ψ := 6689/62500) 294 272
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t334 : ((4328832747/100000000000 : ℚ) : ℝ) ≤ stT294 334 := by
  have hc : ((197781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4328832747/100000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((197781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c335 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((975689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110477/2000000) (δ := 14849/1000000000) (ψ := 6689/62500) 294 272
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t335 : ((266510427431/5000000000000 : ℚ) : ℝ) ≤ stT294 335 := by
  have hc : ((975589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266510427431/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((975589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c336 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((91209/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1371563/5000000) (δ := 14849/1000000000) (ψ := 6689/62500) 294 272
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t336 : ((6218451477/250000000000 : ℚ) : ℝ) ≤ stT294 336 := by
  have hc : ((91189/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6218451477/250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((91189/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c337 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-389569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4927399/10000000) (δ := 14849/1000000000) (ψ := 6689/62500) 294 272
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t337 : ((-42453268543/2000000000000 : ℚ) : ℝ) ≤ stT294 337 := by
  have hc : ((-389669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42453268543/2000000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-389669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c338 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-59717/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7105131/10000000) (δ := 7377/500000000) (ψ := 6689/62500) 294 272
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t338 : ((-129940830597/2500000000000 : ℚ) : ℝ) ≤ stT294 338 := by
  have hc : ((-238893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129940830597/2500000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-238893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c339 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-842427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3215711/5000000) (δ := 14741/1000000000) (ψ := 6689/62500) 294 273
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t339 : ((-228799159701/5000000000000 : ℚ) : ℝ) ≤ stT294 339 := by
  have hc : ((-842527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228799159701/5000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-842527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c340 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-67689/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4266479/10000000) (δ := 7431/500000000) (ψ := 6689/62500) 294 273
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t340 : ((-36736688653/5000000000000 : ℚ) : ℝ) ≤ stT294 340 := by
  have hc : ((-67739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36736688653/5000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-67739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c341 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((665097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2107931/10000000) (δ := 7431/500000000) (ψ := 6689/62500) 294 273
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t341 : ((36011582541/1000000000000 : ℚ) : ℝ) ≤ stT294 341 := by
  have hc : ((664997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36011582541/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((664997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c342 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((999843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44369/10000000) (δ := 14741/1000000000) (ψ := 6689/62500) 294 273
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t342 : ((270299515167/5000000000000 : ℚ) : ℝ) ≤ stT294 342 := by
  have hc : ((999743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270299515167/5000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((999743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c343 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((320061/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2190349/10000000) (δ := 7431/500000000) (ψ := 6689/62500) 294 273
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t343 : ((172789619439/5000000000000 : ℚ) : ℝ) ≤ stT294 343 := by
  have hc : ((320011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172789619439/5000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((320011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c344 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-80269/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4330081/10000000) (δ := 7431/500000000) (ψ := 6689/62500) 294 273
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t344 : ((-10826278329/1250000000000 : ℚ) : ℝ) ≤ stT294 344 := by
  have hc : ((-80319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10826278329/1250000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-80319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c345 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-849301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6463639/10000000) (δ := 7431/500000000) (ψ := 6689/62500) 294 273
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t345 : ((-228651104591/5000000000000 : ℚ) : ℝ) ≤ stT294 345 := by
  have hc : ((-849401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228651104591/5000000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-849401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c346 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-14951/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3558507/5000000) (δ := 14769/1000000000) (ψ := 6689/62500) 294 274
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t346 : ((-32154229641/625000000000 : ℚ) : ℝ) ≤ stT294 346 := by
  have hc : ((-239241/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32154229641/625000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-239241/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c347 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-20731/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1248951/2500000) (δ := 14769/1000000000) (ψ := 6689/62500) 294 274
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t347 : ((-43483149/1953125000 : ℚ) : ℝ) ≤ stT294 347 := by
  have hc : ((-1296/3125 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43483149/1953125000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-1296/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c348 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((406407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -576139/2000000) (δ := 7417/500000000) (ψ := 6689/62500) 294 274
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t348 : ((27225413149/1250000000000 : ℚ) : ℝ) ≤ stT294 348 := by
  have hc : ((406307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27225413149/1250000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((406307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c349 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((476373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192903/2500000) (δ := 14769/1000000000) (ψ := 6689/62500) 294 274
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t349 : ((254969509701/5000000000000 : ℚ) : ℝ) ≤ stT294 349 := by
  have hc : ((476323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254969509701/5000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((476323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c350 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((215379/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 133137/1000000) (δ := 14769/1000000000) (ψ := 6689/62500) 294 274
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t350 : ((28777862697/625000000000 : ℚ) : ℝ) ≤ stT294 350 := by
  have hc : ((107677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28777862697/625000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((107677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c351 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((99059/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1714199/5000000) (δ := 7417/500000000) (ψ := 6689/62500) 294 274
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t351 : ((41286753/3906250000 : ℚ) : ℝ) ≤ stT294 351 := by
  have hc : ((99009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41286753/3906250000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((99009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c352 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-594757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27597/50000) (δ := 14769/1000000000) (ψ := 6689/62500) 294 274
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t352 : ((-158529985357/5000000000000 : ℚ) : ℝ) ≤ stT294 352 := by
  have hc : ((-594857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158529985357/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-594857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c353 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-497513/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7604521/10000000) (δ := 7417/500000000) (ψ := 6689/62500) 294 274
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t353 : ((-264826414061/5000000000000 : ℚ) : ℝ) ≤ stT294 353 := by
  have hc : ((-497563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264826414061/5000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-497563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c354 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-371949/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30121/50000) (δ := 3719/250000000) (ψ := 6689/62500) 294 275
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t354 : ((-39543121701/1000000000000 : ℚ) : ℝ) ≤ stT294 354 := by
  have hc : ((-371999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39543121701/1000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-371999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c355 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-299/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61733/156250) (δ := 3719/250000000) (ψ := 6689/62500) 294 275
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t355 : ((-256562133/500000000000 : ℚ) : ℝ) ≤ stT294 355 := by
  have hc : ((-2417/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256562133/500000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-2417/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c356 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((364703/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1883357/10000000) (δ := 3719/250000000) (ψ := 6689/62500) 294 275
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t356 : ((96632680347/2500000000000 : ℚ) : ℝ) ≤ stT294 356 := by
  have hc : ((364653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96632680347/2500000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((364653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c357 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((997457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89159/5000000) (δ := 3719/250000000) (ψ := 6689/62500) 294 275
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t357 : ((65982147049/1250000000000 : ℚ) : ℝ) ≤ stT294 357 := by
  have hc : ((997357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65982147049/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((997357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c358 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((626529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 111713/500000) (δ := 3719/250000000) (ψ := 6689/62500) 294 275
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t358 : ((82769437341/2500000000000 : ℚ) : ℝ) ≤ stT294 358 := by
  have hc : ((626429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82769437341/2500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((626429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c359 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-17813/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4284469/10000000) (δ := 3719/250000000) (ψ := 6689/62500) 294 275
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t359 : ((-940794239/125000000000 : ℚ) : ℝ) ≤ stT294 359 := by
  have hc : ((-35651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-940794239/125000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-35651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c360 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-102457/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3164509/5000000) (δ := 14727/1000000000) (ψ := 6689/62500) 294 275
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t360 : ((-108012485133/2500000000000 : ℚ) : ℝ) ≤ stT294 360 := by
  have hc : ((-204939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108012485133/2500000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-204939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c361 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-978951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7340129/10000000) (δ := 741/50000000) (ψ := 6689/62500) 294 276
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t361 : ((-128822551529/2500000000000 : ℚ) : ℝ) ≤ stT294 361 := by
  have hc : ((-979051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128822551529/2500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-979051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c362 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-13109/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2653449/5000000) (δ := 14783/1000000000) (ψ := 6689/62500) 294 276
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t362 : ((-13782520347/500000000000 : ℚ) : ℝ) ≤ stT294 362 := by
  have hc : ((-26223/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13782520347/500000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-26223/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c363 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((256177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3279327/10000000) (δ := 14783/1000000000) (ψ := 6689/62500) 294 276
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t363 : ((134405342451/10000000000000 : ℚ) : ℝ) ≤ stT294 363 := by
  have hc : ((256077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134405342451/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((256077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c364 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((876171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628671/5000000) (δ := 14783/1000000000) (ψ := 6689/62500) 294 276
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t364 : ((229592803041/5000000000000 : ℚ) : ℝ) ≤ stT294 364 := by
  have hc : ((876071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229592803041/5000000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((876071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c365 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((954251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75913/1000000) (δ := 741/50000000) (ψ := 6689/62500) 294 276
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t365 : ((499424578873/10000000000000 : ℚ) : ℝ) ≤ stT294 365 := by
  have hc : ((954151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499424578873/10000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((954151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c366 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((22321/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 277009/1000000) (δ := 741/50000000) (ψ := 6689/62500) 294 276
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t366 : ((729046983/31250000000 : ℚ) : ℝ) ≤ stT294 366 := by
  have hc : ((5579/12500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((729046983/31250000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((5579/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c367 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-332939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2387769/5000000) (δ := 14783/1000000000) (ψ := 6689/62500) 294 276
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t367 : ((-43461256461/2500000000000 : ℚ) : ℝ) ≤ stT294 367 := by
  have hc : ((-333039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43461256461/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-333039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c368 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-113549/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3387773/5000000) (δ := 741/50000000) (ψ := 6689/62500) 294 276
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t368 : ((-118396267301/2500000000000 : ℚ) : ℝ) ≤ stT294 368 := by
  have hc : ((-227123/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118396267301/2500000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-227123/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c369 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-233401/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6937847/10000000) (δ := 1489/100000000) (ψ := 6689/62500) 294 277
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t369 : ((-3037922677/62500000000 : ℚ) : ℝ) ≤ stT294 369 := by
  have hc : ((-116713/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3037922677/62500000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-116713/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c370 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-397381/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4948643/10000000) (δ := 1489/100000000) (ψ := 6689/62500) 294 277
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t370 : ((-51660208089/2500000000000 : ℚ) : ℝ) ≤ stT294 370 := by
  have hc : ((-397481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51660208089/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-397481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c371 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((46927/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1482439/5000000) (δ := 1489/100000000) (ψ := 6689/62500) 294 277
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t371 : ((24356788623/1250000000000 : ℚ) : ℝ) ≤ stT294 371 := by
  have hc : ((93829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24356788623/1250000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((93829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c372 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((184633/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197281/2000000) (δ := 1489/100000000) (ψ := 6689/62500) 294 277
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t372 : ((3828689007/80000000000 : ℚ) : ℝ) ≤ stT294 372 := by
  have hc : ((184613/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3828689007/80000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((184613/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c373 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((230777/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123347/1250000) (δ := 1489/100000000) (ψ := 6689/62500) 294 277
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t373 : ((186685579/3906250000 : ℚ) : ℝ) ≤ stT294 373 := by
  have hc : ((14422/15625 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186685579/3906250000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((14422/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c374 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((189613/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2954591/10000000) (δ := 14713/1000000000) (ψ := 6689/62500) 294 277
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t374 : ((98020562981/5000000000000 : ℚ) : ℝ) ≤ stT294 374 := by
  have hc : ((189563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98020562981/5000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((189563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c375 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-385831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2458631/5000000) (δ := 1489/100000000) (ψ := 6689/62500) 294 277
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t375 : ((-99646998269/5000000000000 : ℚ) : ℝ) ≤ stT294 375 := by
  have hc : ((-385931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99646998269/5000000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-385931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c376 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-924247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85933/125000) (δ := 14713/1000000000) (ψ := 6689/62500) 294 277
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t376 : ((-476695915717/10000000000000 : ℚ) : ℝ) ≤ stT294 376 := by
  have hc : ((-924347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-476695915717/10000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-924347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c377 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-23131/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6881163/10000000) (δ := 14797/1000000000) (ψ := 6689/62500) 294 278
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t377 : ((-23828754209/500000000000 : ℚ) : ℝ) ≤ stT294 377 := by
  have hc : ((-46267/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23828754209/500000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-46267/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c378 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-196027/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1233537/2500000) (δ := 14797/1000000000) (ψ := 6689/62500) 294 278
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t378 : ((-20170244913/1000000000000 : ℚ) : ℝ) ≤ stT294 378 := by
  have hc : ((-196077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20170244913/1000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-196077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c379 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((182631/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -598441/2000000) (δ := 7403/500000000) (ψ := 6689/62500) 294 278
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t379 : ((18757093873/1000000000000 : ℚ) : ℝ) ≤ stT294 379 := by
  have hc : ((182581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18757093873/1000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((182581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c380 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((912193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26387/250000) (δ := 7403/500000000) (ψ := 6689/62500) 294 278
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t380 : ((467893675977/10000000000000 : ℚ) : ℝ) ≤ stT294 380 := by
  have hc : ((912093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467893675977/10000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((912093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c381 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((234803/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 438087/5000000) (δ := 14797/1000000000) (ψ := 6689/62500) 294 278
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t381 : ((12028029107/250000000000 : ℚ) : ℝ) ≤ stT294 381 := by
  have hc : ((117389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12028029107/250000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((117389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c382 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((54333/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2802829/10000000) (δ := 7403/500000000) (ψ := 6689/62500) 294 278
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t382 : ((13896378951/625000000000 : ℚ) : ℝ) ≤ stT294 382 := by
  have hc : ((108641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13896378951/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((108641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c383 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-7839/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236217/500000) (δ := 14797/1000000000) (ψ := 6689/62500) 294 278
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t383 : ((-8013652291/500000000000 : ℚ) : ℝ) ≤ stT294 383 := by
  have hc : ((-15683/50000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8013652291/500000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-15683/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c384 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-884571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3320463/5000000) (δ := 14797/1000000000) (ψ := 6689/62500) 294 278
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t384 : ((-451457342681/10000000000000 : ℚ) : ℝ) ≤ stT294 384 := by
  have hc : ((-884671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451457342681/10000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-884671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c385 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-480609/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143109/200000) (δ := 7449/500000000) (ψ := 6689/62500) 294 279
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t385 : ((-15310431127/312500000000 : ℚ) : ℝ) ≤ stT294 385 := by
  have hc : ((-480659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15310431127/312500000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-480659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c386 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-126113/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262443/500000) (δ := 7449/500000000) (ψ := 6689/62500) 294 279
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t386 : ((-32101301103/1250000000000 : ℚ) : ℝ) ≤ stT294 386 := by
  have hc : ((-63069/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32101301103/1250000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-63069/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c387 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((45969/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1673597/5000000) (δ := 2941/200000000) (ψ := 6689/62500) 294 279
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t387 : ((2919645409/250000000000 : ℚ) : ℝ) ≤ stT294 387 := by
  have hc : ((45949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2919645409/250000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((45949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c388 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((836379/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72519/500000) (δ := 7449/500000000) (ψ := 6689/62500) 294 279
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t388 : ((424556268767/10000000000000 : ℚ) : ℝ) ≤ stT294 388 := by
  have hc : ((836279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424556268767/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((836279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c389 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((492223/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44151/1000000) (δ := 7449/500000000) (ψ := 6689/62500) 294 279
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t389 : ((12477077723/250000000000 : ℚ) : ℝ) ≤ stT294 389 := by
  have hc : ((492173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12477077723/250000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((492173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c390 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((119339/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2328549/10000000) (δ := 7449/500000000) (ψ := 6689/62500) 294 279
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t390 : ((60419442711/2000000000000 : ℚ) : ℝ) ≤ stT294 390 := by
  have hc : ((119319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60419442711/2000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((119319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c391 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-22651/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4210737/10000000) (δ := 7449/500000000) (ψ := 6689/62500) 294 279
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t391 : ((-5732611731/1000000000000 : ℚ) : ℝ) ≤ stT294 391 := by
  have hc : ((-22671/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5732611731/1000000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-22671/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c392 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-760747/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1522037/2500000) (δ := 2941/200000000) (ψ := 6689/62500) 294 279
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t392 : ((-384286320219/10000000000000 : ℚ) : ℝ) ≤ stT294 392 := by
  have hc : ((-760847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384286320219/10000000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-760847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c393 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-62443/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3873591/5000000) (δ := 3703/250000000) (ψ := 6689/62500) 294 280
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t393 : ((-63003049949/1250000000000 : ℚ) : ℝ) ≤ stT294 393 := by
  have hc : ((-249797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63003049949/1250000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-249797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c394 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-703943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5879327/10000000) (δ := 14791/1000000000) (ψ := 6689/62500) 294 280
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t394 : ((-354691935099/10000000000000 : ℚ) : ℝ) ≤ stT294 394 := by
  have hc : ((-704043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354691935099/10000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-704043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c395 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-2231/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4016249/10000000) (δ := 14791/1000000000) (ψ := 6689/62500) 294 280
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t395 : ((-900546819/500000000000 : ℚ) : ℝ) ≤ stT294 395 := by
  have hc : ((-8949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-900546819/500000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-8949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c396 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((65007/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2157801/10000000) (δ := 3703/250000000) (ψ := 6689/62500) 294 280
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t396 : ((16331081223/500000000000 : ℚ) : ℝ) ≤ stT294 396 := by
  have hc : ((64997/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16331081223/500000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((64997/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c397 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((992609/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -304131/10000000) (δ := 3703/250000000) (ψ := 6689/62500) 294 280
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t397 : ((99625075893/2000000000000 : ℚ) : ℝ) ≤ stT294 397 := by
  have hc : ((992509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99625075893/2000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((992509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c398 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((815043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 772491/5000000) (δ := 3703/250000000) (ψ := 6689/62500) 294 280
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t398 : ((204246719261/5000000000000 : ℚ) : ℝ) ≤ stT294 398 := by
  have hc : ((814943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204246719261/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((814943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c399 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((106693/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3389391/10000000) (δ := 3703/250000000) (ψ := 6689/62500) 294 280
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t399 : ((26694129259/2500000000000 : ℚ) : ℝ) ≤ stT294 399 := by
  have hc : ((106643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26694129259/2500000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((106643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c400 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-124409/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5229169/10000000) (δ := 14791/1000000000) (ψ := 6689/62500) 294 280
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t400 : ((-31108562217/1250000000000 : ℚ) : ℝ) ≤ stT294 400 := by
  have hc : ((-62217/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31108562217/1250000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-62217/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c401 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-950537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7064391/10000000) (δ := 3703/250000000) (ψ := 6689/62500) 294 280
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t401 : ((-474726253149/10000000000000 : ℚ) : ℝ) ≤ stT294 401 := by
  have hc : ((-950637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474726253149/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-950637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c402 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-914551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3406491/5000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 281
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t402 : ((-91237351901/2000000000000 : ℚ) : ℝ) ≤ stT294 402 := by
  have hc : ((-914651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91237351901/2000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-914651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c403 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-411367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2493437/5000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 281
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t403 : ((-25620815689/1250000000000 : ℚ) : ℝ) ≤ stT294 403 := by
  have hc : ((-411467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25620815689/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-411467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c404 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((11999/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -791331/2500000) (δ := 3721/250000000) (ψ := 6689/62500) 294 281
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t404 : ((596772841/40000000000 : ℚ) : ℝ) ≤ stT294 404 := by
  have hc : ((2399/8000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((596772841/40000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((2399/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c405 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((858067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1348257/10000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 281
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t405 : ((426326376201/10000000000000 : ℚ) : ℝ) ≤ stT294 405 := by
  have hc : ((857967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426326376201/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((857967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c406 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((491401/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464327/10000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 281
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t406 : ((243853079141/5000000000000 : ℚ) : ℝ) ≤ stT294 406 := by
  have hc : ((491351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243853079141/5000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((491351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c407 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((307279/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2272427/10000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 281
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t407 : ((152287577949/5000000000000 : ℚ) : ℝ) ≤ stT294 407 := by
  have hc : ((307229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152287577949/5000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((307229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c408 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-11923/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4076117/10000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 281
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t408 : ((-2956334391/1000000000000 : ℚ) : ℝ) ≤ stT294 408 := by
  have hc : ((-11943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2956334391/1000000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-11943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c409 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-351413/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5875397/10000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 281
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t409 : ((-173787558147/5000000000000 : ℚ) : ℝ) ≤ stT294 409 := by
  have hc : ((-351463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173787558147/5000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-351463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c410 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-997301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7670267/10000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 281
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t410 : ((-98516288973/2000000000000 : ℚ) : ℝ) ≤ stT294 410 := by
  have hc : ((-997401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98516288973/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-997401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c411 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-50029/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6247163/10000000) (δ := 14777/1000000000) (ψ := 6689/62500) 294 282
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t411 : ((-6170146889/156250000000 : ℚ) : ℝ) ≤ stT294 411 := by
  have hc : ((-200141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6170146889/156250000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-200141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c412 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-105999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4461039/10000000) (δ := 7413/500000000) (ψ := 6689/62500) 294 282
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t412 : ((-10449326117/1000000000000 : ℚ) : ℝ) ≤ stT294 412 := by
  have hc : ((-106049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10449326117/1000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-106049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c413 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((59829/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669813/2500000) (δ := 7413/500000000) (ψ := 6689/62500) 294 282
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t413 : ((58867451411/2500000000000 : ℚ) : ℝ) ≤ stT294 413 := by
  have hc : ((119633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58867451411/2500000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((119633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c414 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((935653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28179/312500) (δ := 7413/500000000) (ψ := 6689/62500) 294 282
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t414 : ((459799039569/10000000000000 : ℚ) : ℝ) ≤ stT294 414 := by
  have hc : ((935553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459799039569/10000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((935553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c415 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((939847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 871533/10000000) (δ := 7413/500000000) (ψ := 6689/62500) 294 282
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t415 : ((720785949/15625000000 : ℚ) : ℝ) ≤ stT294 415 := by
  have hc : ((939747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((720785949/15625000000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((939747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c416 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((246099/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2640457/10000000) (δ := 14777/1000000000) (ψ := 6689/62500) 294 282
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t416 : ((12063536421/500000000000 : ℚ) : ℝ) ≤ stT294 416 := by
  have hc : ((246049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12063536421/500000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((246049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c417 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-47529/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 550649/1250000) (δ := 14777/1000000000) (ψ := 6689/62500) 294 282
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t417 : ((-11643668231/1250000000000 : ℚ) : ℝ) ≤ stT294 417 := by
  have hc : ((-23777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11643668231/1250000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-23777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c418 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-780503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192677/312500) (δ := 14777/1000000000) (ψ := 6689/62500) 294 282
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t418 : ((-95451354237/2500000000000 : ℚ) : ℝ) ≤ stT294 418 := by
  have hc : ((-780603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95451354237/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-780603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c419 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-99963/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7786017/10000000) (δ := 1487/100000000) (ψ := 6689/62500) 294 283
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t419 : ((-12210002409/250000000000 : ℚ) : ℝ) ≤ stT294 419 := by
  have hc : ((-99973/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12210002409/250000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-99973/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c420 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-746491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1508481/2500000) (δ := 1487/100000000) (ψ := 6689/62500) 294 283
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t420 : ((-364299825041/10000000000000 : ℚ) : ℝ) ≤ stT294 420 := by
  have hc : ((-746591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364299825041/10000000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-746591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c421 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-143119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214301/500000) (δ := 14733/1000000000) (ψ := 6689/62500) 294 283
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t421 : ((-69800787249/10000000000000 : ℚ) : ℝ) ≤ stT294 421 := by
  have hc : ((-143219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69800787249/10000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-143219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c422 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((526011/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2542233/10000000) (δ := 1487/100000000) (ψ := 6689/62500) 294 283
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t422 : ((32001158439/1250000000000 : ℚ) : ℝ) ≤ stT294 422 := by
  have hc : ((525911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32001158439/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((525911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c423 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((948903/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160527/2000000) (δ := 1487/100000000) (ψ := 6689/62500) 294 283
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t423 : ((57665399931/1250000000000 : ℚ) : ℝ) ≤ stT294 423 := by
  have hc : ((948803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57665399931/1250000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((948803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c424 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((931177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 932921/10000000) (δ := 14733/1000000000) (ψ := 6689/62500) 294 283
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t424 : ((226085048217/5000000000000 : ℚ) : ℝ) ≤ stT294 424 := by
  have hc : ((931077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226085048217/5000000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((931077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c425 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((483853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66609/250000) (δ := 1487/100000000) (ψ := 6689/62500) 294 283
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t425 : ((234654551463/10000000000000 : ℚ) : ℝ) ≤ stT294 425 := by
  have hc : ((483753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234654551463/10000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((483753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c426 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-184837/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4391757/10000000) (δ := 1487/100000000) (ψ := 6689/62500) 294 283
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t426 : ((-44801173187/5000000000000 : ℚ) : ℝ) ≤ stT294 426 := by
  have hc : ((-184937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44801173187/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-184937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c427 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-767703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 764389/1250000) (δ := 14733/1000000000) (ψ := 6689/62500) 294 283
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t427 : ((-185782988501/5000000000000 : ℚ) : ℝ) ≤ stT294 427 := by
  have hc : ((-767803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185782988501/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-767803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c428 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-999969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156687/200000) (δ := 1487/100000000) (ψ := 6689/62500) 294 283
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t428 : ((-483402352461/10000000000000 : ℚ) : ℝ) ≤ stT294 428 := by
  have hc : ((-1000069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483402352461/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-1000069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c429 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-15573/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -615827/1000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 284
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t429 : ((-60157503/1600000000 : ℚ) : ℝ) ≤ stT294 429 := by
  have hc : ((-623/800 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60157503/1600000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-623/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c430 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-41299/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4446969/10000000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 284
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t430 : ((-19925798517/2000000000000 : ℚ) : ℝ) ≤ stT294 430 := by
  have hc : ((-41319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19925798517/2000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-41319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c431 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((22863/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2739711/10000000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 284
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t431 : ((5505155007/250000000000 : ℚ) : ℝ) ≤ stT294 431 := by
  have hc : ((11429/25000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5505155007/250000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((11429/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c432 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((457651/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1036349/10000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 284
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t432 : ((1761306249/40000000000 : ℚ) : ℝ) ≤ stT294 432 := by
  have hc : ((457601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1761306249/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((457601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c433 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((241257/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 331559/5000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 284
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t433 : ((7245538813/156250000000 : ℚ) : ℝ) ≤ stT294 433 := by
  have hc : ((15077/15625 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7245538813/156250000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((15077/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c434 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((587001/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294827/1250000) (δ := 7381/500000000) (ψ := 6689/62500) 294 284
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t434 : ((56344256703/2000000000000 : ℚ) : ℝ) ≤ stT294 434 := by
  have hc : ((586901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56344256703/2000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((586901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c435 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-49271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4050219/10000000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 284
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t435 : ((-2958952143/1250000000000 : ℚ) : ℝ) ≤ stT294 435 := by
  have hc : ((-49371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2958952143/1250000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-49371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c436 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-662667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2868963/5000000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 284
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t436 : ((-158704197519/5000000000000 : ℚ) : ℝ) ≤ stT294 436 := by
  have hc : ((-662767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158704197519/5000000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-662767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c437 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-98509/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7421737/10000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 284
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t437 : ((-9425608287/200000000000 : ℚ) : ℝ) ≤ stT294 437 := by
  have hc : ((-98519/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9425608287/200000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-98519/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c438 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-878001/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6606163/10000000) (δ := 3687/250000000) (ψ := 6689/62500) 294 285
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t438 : ((-419573341719/10000000000000 : ℚ) : ℝ) ≤ stT294 438 := by
  have hc : ((-878101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419573341719/10000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-878101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c439 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-15621/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1232499/2500000) (δ := 2971/200000000) (ψ := 6689/62500) 294 285
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t439 : ((-238637/12800000 : ℚ) : ℝ) ≤ stT294 439 := by
  have hc : ((-25/64 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238637/12800000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-25/64 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c440 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((264549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65153/200000) (δ := 3687/250000000) (ψ := 6689/62500) 294 285
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t440 : ((126071036219/10000000000000 : ℚ) : ℝ) ≤ stT294 440 := by
  have hc : ((264449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126071036219/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((264449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c441 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((160937/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1589127/10000000) (δ := 2971/200000000) (ψ := 6689/62500) 294 285
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t441 : ((7662706623/200000000000 : ℚ) : ℝ) ≤ stT294 441 := by
  have hc : ((160917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7662706623/200000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((160917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c442 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((499771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591/78125) (δ := 2971/200000000) (ψ := 6689/62500) 294 285
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t442 : ((237692793371/5000000000000 : ℚ) : ℝ) ≤ stT294 442 := by
  have hc : ((499721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237692793371/5000000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((499721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c443 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((153653/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69467/400000) (δ := 3687/250000000) (ψ := 6689/62500) 294 285
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t443 : ((36496594581/1000000000000 : ℚ) : ℝ) ≤ stT294 443 := by
  have hc : ((153633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36496594581/1000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((153633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c444 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((211603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3393953/10000000) (δ := 3687/250000000) (ψ := 6689/62500) 294 285
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t444 : ((50187335367/5000000000000 : ℚ) : ℝ) ≤ stT294 444 := by
  have hc : ((211503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50187335367/5000000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((211503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c445 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-433341/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2523741/5000000) (δ := 2971/200000000) (ψ := 6689/62500) 294 285
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t445 : ((-102735486143/5000000000000 : ℚ) : ℝ) ≤ stT294 445 := by
  have hc : ((-433441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102735486143/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-433441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c446 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-894869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6697337/10000000) (δ := 3687/250000000) (ψ := 6689/62500) 294 285
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t446 : ((-211890175533/5000000000000 : ℚ) : ℝ) ≤ stT294 446 := by
  have hc : ((-894969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211890175533/5000000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-894969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c447 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-196179/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184113/250000) (δ := 2971/200000000) (ψ := 6689/62500) 294 286
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t447 : ((-11599873477/250000000000 : ℚ) : ℝ) ≤ stT294 447 := by
  have hc : ((-196199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11599873477/250000000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-196199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c448 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-657887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -178813/312500) (δ := 3687/250000000) (ψ := 6689/62500) 294 286
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t448 : ((-38858738259/1250000000000 : ℚ) : ℝ) ≤ stT294 448 := by
  have hc : ((-657987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38858738259/1250000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-657987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c449 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-62467/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204163/500000) (δ := 3687/250000000) (ψ := 6689/62500) 294 286
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t449 : ((-2952724431/1000000000000 : ℚ) : ℝ) ≤ stT294 449 := by
  have hc : ((-62567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2952724431/1000000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-62567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c450 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((139413/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489621/2000000) (δ := 2971/200000000) (ψ := 6689/62500) 294 286
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t450 : ((4106753797/156250000000 : ℚ) : ℝ) ≤ stT294 450 := by
  have hc : ((34847/62500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4106753797/156250000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((34847/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c451 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((236783/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102069/1250000) (δ := 2971/200000000) (ψ := 6689/62500) 294 286
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t451 : ((55742421899/1250000000000 : ℚ) : ℝ) ≤ stT294 451 := by
  have hc : ((118379/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55742421899/1250000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((118379/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c452 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((947801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 405663/5000000) (δ := 2971/200000000) (ψ := 6689/62500) 294 286
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t452 : ((11144016059/250000000000 : ℚ) : ℝ) ≤ stT294 452 := by
  have hc : ((947701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11144016059/250000000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((947701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c453 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((140443/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608919/2500000) (δ := 2971/200000000) (ψ := 6689/62500) 294 286
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t453 : ((412337457/15625000000 : ℚ) : ℝ) ≤ stT294 453 := by
  have hc : ((70209/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((412337457/15625000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((70209/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c454 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-51721/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4056351/10000000) (δ := 2971/200000000) (ψ := 6689/62500) 294 286
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t454 : ((-6080209751/2500000000000 : ℚ) : ℝ) ≤ stT294 454 := by
  have hc : ((-51821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6080209751/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-51821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c455 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-643171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5673571/10000000) (δ := 3687/250000000) (ψ := 6689/62500) 294 286
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t455 : ((-37696323871/1250000000000 : ℚ) : ℝ) ≤ stT294 455 := by
  have hc : ((-643271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37696323871/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-643271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c456 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-97441/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 728719/1000000) (δ := 3687/250000000) (ψ := 6689/62500) 294 286
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t456 : ((-45635621143/1000000000000 : ℚ) : ℝ) ≤ stT294 456 := by
  have hc : ((-97451/100000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45635621143/1000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-97451/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c457 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-914191/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1702689/2500000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 287
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t457 : ((-427687958271/10000000000000 : ℚ) : ℝ) ≤ stT294 457 := by
  have hc : ((-914291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427687958271/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-914291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c458 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-244473/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5204193/10000000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 287
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t458 : ((-11425826221/500000000000 : ℚ) : ℝ) ≤ stT294 458 := by
  have hc : ((-244523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11425826221/500000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-244523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c459 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((64997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900271/2500000) (δ := 7381/500000000) (ψ := 6689/62500) 294 287
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t459 : ((757866543/125000000000 : ℚ) : ℝ) ≤ stT294 459 := by
  have hc : ((64947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((757866543/125000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((64947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c460 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((348127/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2001577/10000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 287
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t460 : ((40572899351/1250000000000 : ℚ) : ℝ) ≤ stT294 460 := by
  have hc : ((348077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40572899351/1250000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((348077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c461 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((493439/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405451/10000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 287
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t461 : ((114896976597/2500000000000 : ℚ) : ℝ) ≤ stT294 461 := by
  have hc : ((493389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114896976597/2500000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((493389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c462 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((889357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1187147/10000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 287
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t462 : ((206859852597/5000000000000 : ℚ) : ℝ) ≤ stT294 462 := by
  have hc : ((889257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206859852597/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((889257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c463 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((444173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694091/2500000) (δ := 7381/500000000) (ψ := 6689/62500) 294 287
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t463 : ((206378041947/10000000000000 : ℚ) : ℝ) ≤ stT294 463 := by
  have hc : ((444073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206378041947/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((444073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c464 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-173177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2181063/5000000) (δ := 14841/1000000000) (ψ := 6689/62500) 294 287
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t464 : ((-80441941203/10000000000000 : ℚ) : ℝ) ≤ stT294 464 := by
  have hc : ((-173277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80441941203/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-173277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c465 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-36111/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1486127/2500000) (δ := 7381/500000000) (ψ := 6689/62500) 294 287
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t465 : ((-4187099431/125000000000 : ℚ) : ℝ) ≤ stT294 465 := by
  have hc : ((-9029/12500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4187099431/125000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-9029/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c466 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-123909/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1504687/2000000) (δ := 7381/500000000) (ψ := 6689/62500) 294 287
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t466 : ((-57405643503/1250000000000 : ℚ) : ℝ) ≤ stT294 466 := by
  have hc : ((-247843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57405643503/1250000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-247843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c467 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-43927/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3304491/5000000) (δ := 14869/1000000000) (ψ := 6689/62500) 294 288
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t467 : ((-1016465667/25000000000 : ℚ) : ℝ) ≤ stT294 467 := by
  have hc : ((-10983/12500 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1016465667/25000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-10983/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c468 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-107373/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5036817/10000000) (δ := 14869/1000000000) (ψ := 6689/62500) 294 288
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t468 : ((-24822416449/1250000000000 : ℚ) : ℝ) ≤ stT294 468 := by
  have hc : ((-53699/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24822416449/1250000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-53699/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c469 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((91291/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86699/250000) (δ := 7367/500000000) (ψ := 6689/62500) 294 288
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t469 : ((42131170437/5000000000000 : ℚ) : ℝ) ≤ stT294 469 := by
  have hc : ((91241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42131170437/5000000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((91241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c470 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((724151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1902483/10000000) (δ := 14869/1000000000) (ψ := 6689/62500) 294 288
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t470 : ((66795876903/2000000000000 : ℚ) : ℝ) ≤ stT294 470 := by
  have hc : ((724051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66795876903/2000000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((724051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c471 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((990749/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170157/5000000) (δ := 14869/1000000000) (ψ := 6689/62500) 294 288
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t471 : ((18258651719/400000000000 : ℚ) : ℝ) ≤ stT294 471 := by
  have hc : ((990649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18258651719/400000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((990649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c472 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((176709/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1218547/10000000) (δ := 7367/500000000) (ψ := 6689/62500) 294 288
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t472 : ((81327649743/2000000000000 : ℚ) : ℝ) ≤ stT294 472 := by
  have hc : ((176689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81327649743/2000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((176689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c473 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((55623/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2774101/10000000) (δ := 7367/500000000) (ψ := 6689/62500) 294 288
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t473 : ((255697079/12500000000 : ℚ) : ℝ) ≤ stT294 473 := by
  have hc : ((111221/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255697079/12500000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((111221/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c474 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-159093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4326421/10000000) (δ := 7367/500000000) (ψ := 6689/62500) 294 288
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t474 : ((-18279972997/2500000000000 : ℚ) : ℝ) ≤ stT294 474 := by
  have hc : ((-159193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18279972997/2500000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-159193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c475 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-702837/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2937717/5000000) (δ := 14869/1000000000) (ψ := 6689/62500) 294 288
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t475 : ((-20158124349/625000000000 : ℚ) : ℝ) ≤ stT294 475 := by
  have hc : ((-702937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20158124349/625000000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-702937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c476 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-985049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7421139/10000000) (δ := 14869/1000000000) (ψ := 6689/62500) 294 288
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t476 : ((-9030860883/200000000000 : ℚ) : ℝ) ≤ stT294 476 := by
  have hc : ((-985149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9030860883/200000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-985149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c477 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-180621/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3372177/5000000) (δ := 14827/1000000000) (ψ := 6689/62500) 294 289
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t477 : ((-82709914029/2000000000000 : ℚ) : ℝ) ≤ stT294 477 := by
  have hc : ((-180641/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82709914029/2000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-180641/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c478 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-244621/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5205043/10000000) (δ := 1847/125000000) (ψ := 6689/62500) 294 289
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t478 : ((-11191006869/500000000000 : ℚ) : ℝ) ≤ stT294 478 := by
  have hc : ((-244671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11191006869/500000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-244671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c479 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((102997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45863/125000) (δ := 1847/125000000) (ψ := 6689/62500) 294 289
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t479 : ((47014771167/10000000000000 : ℚ) : ℝ) ≤ stT294 479 := by
  have hc : ((102897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47014771167/10000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((102897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c480 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((328317/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -534031/2500000) (δ := 1847/125000000) (ψ := 6689/62500) 294 289
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t480 : ((29966509629/1000000000000 : ℚ) : ℝ) ≤ stT294 480 := by
  have hc : ((328267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29966509629/1000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((328267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c481 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((194143/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151629/2500000) (δ := 14827/1000000000) (ψ := 6689/62500) 294 289
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t481 : ((2212808077/50000000000 : ℚ) : ℝ) ≤ stT294 481 := by
  have hc : ((194123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2212808077/50000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((194123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c482 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((116631/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 460003/5000000) (δ := 1847/125000000) (ψ := 6689/62500) 294 289
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t482 : ((106236421419/2500000000000 : ℚ) : ℝ) ≤ stT294 482 := by
  have hc : ((233237/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106236421419/2500000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((233237/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c483 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((559249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2443293/10000000) (δ := 14827/1000000000) (ψ := 6689/62500) 294 289
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t483 : ((50884236447/2000000000000 : ℚ) : ℝ) ≤ stT294 483 := by
  have hc : ((559149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50884236447/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((559149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c484 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-14601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1981747/5000000) (δ := 1847/125000000) (ψ := 6689/62500) 294 289
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t484 : ((-3341140373/5000000000000 : ℚ) : ℝ) ≤ stT294 484 := by
  have hc : ((-14701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3341140373/5000000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-14701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c485 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-145541/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274023/500000) (δ := 14827/1000000000) (ψ := 6689/62500) 294 289
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t485 : ((-33049086291/1250000000000 : ℚ) : ℝ) ≤ stT294 485 := by
  have hc : ((-72783/125000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33049086291/1250000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-72783/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c486 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-941471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6994413/10000000) (δ := 14827/1000000000) (ψ := 6689/62500) 294 289
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t486 : ((-42710602131/1000000000000 : ℚ) : ℝ) ≤ stT294 486 := by
  have hc : ((-941571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42710602131/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-941571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c487 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-120783/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7202757/10000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t487 : ((-13684439013/312500000000 : ℚ) : ℝ) ≤ stT294 487 := by
  have hc : ((-241591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13684439013/312500000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-241591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c488 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-324863/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1423763/2500000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 290
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t488 : ((-147081291927/5000000000000 : ℚ) : ℝ) ≤ stT294 488 := by
  have hc : ((-324913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147081291927/5000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-324913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c489 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-105211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4190507/10000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 290
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t489 : ((-5952914897/1250000000000 : ℚ) : ℝ) ≤ stT294 489 := by
  have hc : ((-105311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5952914897/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-105311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c490 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((475213/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -107559/400000) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t490 : ((214633723089/10000000000000 : ℚ) : ℝ) ≤ stT294 490 := by
  have hc : ((475113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214633723089/10000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((475113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c491 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((888751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1190457/10000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t491 : ((401041975743/10000000000000 : ℚ) : ℝ) ≤ stT294 491 := by
  have hc : ((888651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401041975743/10000000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((888651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c492 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((124071/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152487/5000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t492 : ((55929789789/1250000000000 : ℚ) : ℝ) ≤ stT294 492 := by
  have hc : ((248117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55929789789/1250000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((248117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c493 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((752513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 898659/5000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t493 : ((338869509701/10000000000000 : ℚ) : ℝ) ≤ stT294 493 := by
  have hc : ((752413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338869509701/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((752413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c494 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((253317/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1643361/5000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t494 : ((113927645857/10000000000000 : ℚ) : ℝ) ≤ stT294 494 := by
  have hc : ((253217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113927645857/10000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((253217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c495 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-82999/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4773039/10000000) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t495 : ((-2332284263/156250000000 : ℚ) : ℝ) ≤ stT294 495 := by
  have hc : ((-5189/15625 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2332284263/156250000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-5189/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c496 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-802677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195513/312500) (δ := 3721/250000000) (ψ := 6689/62500) 294 290
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t496 : ((-180229055939/5000000000000 : ℚ) : ℝ) ≤ stT294 496 := by
  have hc : ((-802777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180229055939/5000000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-802777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c497 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-998901/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7736779/10000000) (δ := 14719/1000000000) (ψ := 6689/62500) 294 290
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t497 : ((-224056943281/5000000000000 : ℚ) : ℝ) ≤ stT294 497 := by
  have hc : ((-999001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224056943281/5000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-999001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c498 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-171123/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3246917/5000000) (δ := 14791/1000000000) (ψ := 6689/62500) 294 291
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t498 : ((-76691060873/2000000000000 : ℚ) : ℝ) ≤ stT294 498 := by
  have hc : ((-171143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76691060873/2000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-171143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c499 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-423199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156857/312500) (δ := 14791/1000000000) (ψ := 6689/62500) 294 291
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t499 : ((-94747438469/5000000000000 : ℚ) : ℝ) ≤ stT294 499 := by
  have hc : ((-423299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94747438469/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-423299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_c500 :
    |Real.cos (((294 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((30207/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1773977/5000000) (δ := 14791/1000000000) (ψ := 6689/62500) 294 291
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st294_t500 : ((13500018831/2000000000000 : ℚ) : ℝ) ≤ stT294 500 := by
  have hc : ((30187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((294 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((6689/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st294_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13500018831/2000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((30187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st294_p1 : ((497089/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT294 (i+1) := by
  rw [Finset.sum_range_one]
  exact st294_t1

theorem st294_p2 : ((955829802473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT294 (i+1))
      = (∑ i ∈ Finset.range 1, stT294 (i+1)) + stT294 2 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 1
    simpa using h
  have hprev := st294_p1
  have hstep := st294_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p3 : ((-29827568537/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT294 (i+1))
      = (∑ i ∈ Finset.range 2, stT294 (i+1)) + stT294 3 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 2
    simpa using h
  have hprev := st294_p2
  have hstep := st294_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p4 : ((116880931463/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT294 (i+1))
      = (∑ i ∈ Finset.range 3, stT294 (i+1)) + stT294 4 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 3
    simpa using h
  have hprev := st294_p3
  have hstep := st294_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p5 : ((2391898781/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT294 (i+1))
      = (∑ i ∈ Finset.range 4, stT294 (i+1)) + stT294 5 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 4
    simpa using h
  have hprev := st294_p4
  have hstep := st294_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p6 : ((1492040294491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT294 (i+1))
      = (∑ i ∈ Finset.range 5, stT294 (i+1)) + stT294 6 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 5
    simpa using h
  have hprev := st294_p5
  have hstep := st294_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p7 : ((3335835679681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT294 (i+1))
      = (∑ i ∈ Finset.range 6, stT294 (i+1)) + stT294 7 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 6
    simpa using h
  have hprev := st294_p6
  have hstep := st294_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p8 : ((2968843714947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT294 (i+1))
      = (∑ i ∈ Finset.range 7, stT294 (i+1)) + stT294 8 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 7
    simpa using h
  have hprev := st294_p7
  have hstep := st294_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p9 : ((6857590671237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT294 (i+1))
      = (∑ i ∈ Finset.range 8, stT294 (i+1)) + stT294 9 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 8
    simpa using h
  have hprev := st294_p8
  have hstep := st294_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p10 : ((6352729826259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT294 (i+1))
      = (∑ i ∈ Finset.range 9, stT294 (i+1)) + stT294 10 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 9
    simpa using h
  have hprev := st294_p9
  have hstep := st294_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p11 : ((3781798095973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT294 (i+1))
      = (∑ i ∈ Finset.range 10, stT294 (i+1)) + stT294 11 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 10
    simpa using h
  have hprev := st294_p10
  have hstep := st294_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p12 : ((3730800735141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT294 (i+1))
      = (∑ i ∈ Finset.range 11, stT294 (i+1)) + stT294 12 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 11
    simpa using h
  have hprev := st294_p11
  have hstep := st294_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p13 : ((5117388485391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT294 (i+1))
      = (∑ i ∈ Finset.range 12, stT294 (i+1)) + stT294 13 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 12
    simpa using h
  have hprev := st294_p12
  have hstep := st294_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p14 : ((7613876359719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT294 (i+1))
      = (∑ i ∈ Finset.range 13, stT294 (i+1)) + stT294 14 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 13
    simpa using h
  have hprev := st294_p13
  have hstep := st294_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p15 : ((3383604300381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT294 (i+1))
      = (∑ i ∈ Finset.range 14, stT294 (i+1)) + stT294 15 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 14
    simpa using h
  have hprev := st294_p14
  have hstep := st294_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p16 : ((19524073103/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT294 (i+1))
      = (∑ i ∈ Finset.range 15, stT294 (i+1)) + stT294 16 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 15
    simpa using h
  have hprev := st294_p15
  have hstep := st294_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p17 : ((3957446053931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT294 (i+1))
      = (∑ i ∈ Finset.range 16, stT294 (i+1)) + stT294 17 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 16
    simpa using h
  have hprev := st294_p16
  have hstep := st294_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p18 : ((4282715089931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT294 (i+1))
      = (∑ i ∈ Finset.range 17, stT294 (i+1)) + stT294 18 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 17
    simpa using h
  have hprev := st294_p17
  have hstep := st294_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p19 : ((2197714658749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT294 (i+1))
      = (∑ i ∈ Finset.range 18, stT294 (i+1)) + stT294 19 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 18
    simpa using h
  have hprev := st294_p18
  have hstep := st294_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p20 : ((5617782051249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT294 (i+1))
      = (∑ i ∈ Finset.range 19, stT294 (i+1)) + stT294 20 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 19
    simpa using h
  have hprev := st294_p19
  have hstep := st294_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p21 : ((716821812183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT294 (i+1))
      = (∑ i ∈ Finset.range 20, stT294 (i+1)) + stT294 21 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 20
    simpa using h
  have hprev := st294_p20
  have hstep := st294_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p22 : ((2008295043939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT294 (i+1))
      = (∑ i ∈ Finset.range 21, stT294 (i+1)) + stT294 22 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 21
    simpa using h
  have hprev := st294_p21
  have hstep := st294_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p23 : ((166758707953/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT294 (i+1))
      = (∑ i ∈ Finset.range 22, stT294 (i+1)) + stT294 23 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 22
    simpa using h
  have hprev := st294_p22
  have hstep := st294_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p24 : ((285515475181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT294 (i+1))
      = (∑ i ∈ Finset.range 23, stT294 (i+1)) + stT294 24 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 23
    simpa using h
  have hprev := st294_p23
  have hstep := st294_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p25 : ((-1053331861819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT294 (i+1))
      = (∑ i ∈ Finset.range 24, stT294 (i+1)) + stT294 25 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 24
    simpa using h
  have hprev := st294_p24
  have hstep := st294_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p26 : ((-114010881577/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT294 (i+1))
      = (∑ i ∈ Finset.range 25, stT294 (i+1)) + stT294 26 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 25
    simpa using h
  have hprev := st294_p25
  have hstep := st294_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p27 : ((-90364857997/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT294 (i+1))
      = (∑ i ∈ Finset.range 26, stT294 (i+1)) + stT294 27 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 26
    simpa using h
  have hprev := st294_p26
  have hstep := st294_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p28 : ((-143324077239/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT294 (i+1))
      = (∑ i ∈ Finset.range 27, stT294 (i+1)) + stT294 28 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 27
    simpa using h
  have hprev := st294_p27
  have hstep := st294_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p29 : ((-500668877183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT294 (i+1))
      = (∑ i ∈ Finset.range 28, stT294 (i+1)) + stT294 29 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 28
    simpa using h
  have hprev := st294_p28
  have hstep := st294_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p30 : ((-628005457451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT294 (i+1))
      = (∑ i ∈ Finset.range 29, stT294 (i+1)) + stT294 30 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 29
    simpa using h
  have hprev := st294_p29
  have hstep := st294_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p31 : ((-1087344471897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT294 (i+1))
      = (∑ i ∈ Finset.range 30, stT294 (i+1)) + stT294 31 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 30
    simpa using h
  have hprev := st294_p30
  have hstep := st294_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p32 : ((-28425301739/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT294 (i+1))
      = (∑ i ∈ Finset.range 31, stT294 (i+1)) + stT294 32 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 31
    simpa using h
  have hprev := st294_p31
  have hstep := st294_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p33 : ((-651764116853/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT294 (i+1))
      = (∑ i ∈ Finset.range 32, stT294 (i+1)) + stT294 33 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 32
    simpa using h
  have hprev := st294_p32
  have hstep := st294_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p34 : ((-898089349777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT294 (i+1))
      = (∑ i ∈ Finset.range 33, stT294 (i+1)) + stT294 34 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 33
    simpa using h
  have hprev := st294_p33
  have hstep := st294_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p35 : ((-916348346183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT294 (i+1))
      = (∑ i ∈ Finset.range 34, stT294 (i+1)) + stT294 35 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 34
    simpa using h
  have hprev := st294_p34
  have hstep := st294_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p36 : ((-135681676761/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT294 (i+1))
      = (∑ i ∈ Finset.range 35, stT294 (i+1)) + stT294 36 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 35
    simpa using h
  have hprev := st294_p35
  have hstep := st294_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p37 : ((-234516581291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT294 (i+1))
      = (∑ i ∈ Finset.range 36, stT294 (i+1)) + stT294 37 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 36
    simpa using h
  have hprev := st294_p36
  have hstep := st294_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p38 : ((-587648226763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT294 (i+1))
      = (∑ i ∈ Finset.range 37, stT294 (i+1)) + stT294 38 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 37
    simpa using h
  have hprev := st294_p37
  have hstep := st294_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p39 : ((-1921772337883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT294 (i+1))
      = (∑ i ∈ Finset.range 38, stT294 (i+1)) + stT294 39 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 38
    simpa using h
  have hprev := st294_p38
  have hstep := st294_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p40 : ((-649921941561/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT294 (i+1))
      = (∑ i ∈ Finset.range 39, stT294 (i+1)) + stT294 40 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 39
    simpa using h
  have hprev := st294_p39
  have hstep := st294_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p41 : ((-3281448860411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT294 (i+1))
      = (∑ i ∈ Finset.range 40, stT294 (i+1)) + stT294 41 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 40
    simpa using h
  have hprev := st294_p40
  have hstep := st294_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p42 : ((-109754055293/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT294 (i+1))
      = (∑ i ∈ Finset.range 41, stT294 (i+1)) + stT294 42 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 41
    simpa using h
  have hprev := st294_p41
  have hstep := st294_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p43 : ((-137696570001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT294 (i+1))
      = (∑ i ∈ Finset.range 42, stT294 (i+1)) + stT294 43 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 42
    simpa using h
  have hprev := st294_p42
  have hstep := st294_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p44 : ((741948092591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT294 (i+1))
      = (∑ i ∈ Finset.range 43, stT294 (i+1)) + stT294 44 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 43
    simpa using h
  have hprev := st294_p43
  have hstep := st294_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p45 : ((193324829753/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT294 (i+1))
      = (∑ i ∈ Finset.range 44, stT294 (i+1)) + stT294 45 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 44
    simpa using h
  have hprev := st294_p44
  have hstep := st294_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p46 : ((2935350440651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT294 (i+1))
      = (∑ i ∈ Finset.range 45, stT294 (i+1)) + stT294 46 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 45
    simpa using h
  have hprev := st294_p45
  have hstep := st294_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p47 : ((3883527719313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT294 (i+1))
      = (∑ i ∈ Finset.range 46, stT294 (i+1)) + stT294 47 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 46
    simpa using h
  have hprev := st294_p46
  have hstep := st294_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p48 : ((4920055721313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT294 (i+1))
      = (∑ i ∈ Finset.range 47, stT294 (i+1)) + stT294 48 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 47
    simpa using h
  have hprev := st294_p47
  have hstep := st294_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p49 : ((6138995355631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT294 (i+1))
      = (∑ i ∈ Finset.range 48, stT294 (i+1)) + stT294 49 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 48
    simpa using h
  have hprev := st294_p48
  have hstep := st294_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p50 : ((376174999157/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT294 (i+1))
      = (∑ i ∈ Finset.range 49, stT294 (i+1)) + stT294 50 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 49
    simpa using h
  have hprev := st294_p49
  have hstep := st294_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p51 : ((443893520153/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT294 (i+1))
      = (∑ i ∈ Finset.range 50, stT294 (i+1)) + stT294 51 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 50
    simpa using h
  have hprev := st294_p50
  have hstep := st294_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p52 : ((981295731481/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT294 (i+1))
      = (∑ i ∈ Finset.range 51, stT294 (i+1)) + stT294 52 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 51
    simpa using h
  have hprev := st294_p51
  have hstep := st294_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p53 : ((1978252483009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT294 (i+1))
      = (∑ i ∈ Finset.range 52, stT294 (i+1)) + stT294 53 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 52
    simpa using h
  have hprev := st294_p52
  have hstep := st294_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p54 : ((8983053972813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT294 (i+1))
      = (∑ i ∈ Finset.range 53, stT294 (i+1)) + stT294 54 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 53
    simpa using h
  have hprev := st294_p53
  have hstep := st294_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p55 : ((7636092715613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT294 (i+1))
      = (∑ i ∈ Finset.range 54, stT294 (i+1)) + stT294 55 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 54
    simpa using h
  have hprev := st294_p54
  have hstep := st294_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p56 : ((6952670571831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT294 (i+1))
      = (∑ i ∈ Finset.range 55, stT294 (i+1)) + stT294 56 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 55
    simpa using h
  have hprev := st294_p55
  have hstep := st294_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p57 : ((7636678764611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT294 (i+1))
      = (∑ i ∈ Finset.range 56, stT294 (i+1)) + stT294 57 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 56
    simpa using h
  have hprev := st294_p56
  have hstep := st294_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p58 : ((8936399408243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT294 (i+1))
      = (∑ i ∈ Finset.range 57, stT294 (i+1)) + stT294 58 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 57
    simpa using h
  have hprev := st294_p57
  have hstep := st294_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p59 : ((4579153845091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT294 (i+1))
      = (∑ i ∈ Finset.range 58, stT294 (i+1)) + stT294 59 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 58
    simpa using h
  have hprev := st294_p58
  have hstep := st294_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p60 : ((7969238036427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT294 (i+1))
      = (∑ i ∈ Finset.range 59, stT294 (i+1)) + stT294 60 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 59
    simpa using h
  have hprev := st294_p59
  have hstep := st294_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p61 : ((3651297355521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT294 (i+1))
      = (∑ i ∈ Finset.range 60, stT294 (i+1)) + stT294 61 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 60
    simpa using h
  have hprev := st294_p60
  have hstep := st294_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p62 : ((1667849907461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT294 (i+1))
      = (∑ i ∈ Finset.range 61, stT294 (i+1)) + stT294 62 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 61
    simpa using h
  have hprev := st294_p61
  have hstep := st294_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p63 : ((2264555511983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT294 (i+1))
      = (∑ i ∈ Finset.range 62, stT294 (i+1)) + stT294 63 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 62
    simpa using h
  have hprev := st294_p62
  have hstep := st294_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p64 : ((7976472432533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT294 (i+1))
      = (∑ i ∈ Finset.range 63, stT294 (i+1)) + stT294 64 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 63
    simpa using h
  have hprev := st294_p63
  have hstep := st294_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p65 : ((1505356604957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT294 (i+1))
      = (∑ i ∈ Finset.range 64, stT294 (i+1)) + stT294 65 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 64
    simpa using h
  have hprev := st294_p64
  have hstep := st294_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p66 : ((8744271445787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT294 (i+1))
      = (∑ i ∈ Finset.range 65, stT294 (i+1)) + stT294 66 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 65
    simpa using h
  have hprev := st294_p65
  have hstep := st294_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p67 : ((8568718761067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT294 (i+1))
      = (∑ i ∈ Finset.range 66, stT294 (i+1)) + stT294 67 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 66
    simpa using h
  have hprev := st294_p66
  have hstep := st294_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p68 : ((1500972430661/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT294 (i+1))
      = (∑ i ∈ Finset.range 67, stT294 (i+1)) + stT294 68 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 67
    simpa using h
  have hprev := st294_p67
  have hstep := st294_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p69 : ((8463396766207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT294 (i+1))
      = (∑ i ∈ Finset.range 68, stT294 (i+1)) + stT294 69 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 68
    simpa using h
  have hprev := st294_p68
  have hstep := st294_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p70 : ((8662542069883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT294 (i+1))
      = (∑ i ∈ Finset.range 69, stT294 (i+1)) + stT294 70 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 69
    simpa using h
  have hprev := st294_p69
  have hstep := st294_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p71 : ((7557947096947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT294 (i+1))
      = (∑ i ∈ Finset.range 70, stT294 (i+1)) + stT294 71 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 70
    simpa using h
  have hprev := st294_p70
  have hstep := st294_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p72 : ((4266653774639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT294 (i+1))
      = (∑ i ∈ Finset.range 71, stT294 (i+1)) + stT294 72 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 71
    simpa using h
  have hprev := st294_p71
  have hstep := st294_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p73 : ((4230688184291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT294 (i+1))
      = (∑ i ∈ Finset.range 72, stT294 (i+1)) + stT294 73 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 72
    simpa using h
  have hprev := st294_p72
  have hstep := st294_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p74 : ((7629736835351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT294 (i+1))
      = (∑ i ∈ Finset.range 73, stT294 (i+1)) + stT294 74 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 73
    simpa using h
  have hprev := st294_p73
  have hstep := st294_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p75 : ((8783764799951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT294 (i+1))
      = (∑ i ∈ Finset.range 74, stT294 (i+1)) + stT294 75 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 74
    simpa using h
  have hprev := st294_p74
  have hstep := st294_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p76 : ((7971050151819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT294 (i+1))
      = (∑ i ∈ Finset.range 75, stT294 (i+1)) + stT294 76 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 75
    simpa using h
  have hprev := st294_p75
  have hstep := st294_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p77 : ((4034203873287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT294 (i+1))
      = (∑ i ∈ Finset.range 76, stT294 (i+1)) + stT294 77 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 76
    simpa using h
  have hprev := st294_p76
  have hstep := st294_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p78 : ((542240307367/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT294 (i+1))
      = (∑ i ∈ Finset.range 77, stT294 (i+1)) + stT294 78 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 77
    simpa using h
  have hprev := st294_p77
  have hstep := st294_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p79 : ((477486711343/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT294 (i+1))
      = (∑ i ∈ Finset.range 78, stT294 (i+1)) + stT294 79 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 78
    simpa using h
  have hprev := st294_p78
  have hstep := st294_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p80 : ((218604062259/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT294 (i+1))
      = (∑ i ∈ Finset.range 79, stT294 (i+1)) + stT294 80 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 79
    simpa using h
  have hprev := st294_p79
  have hstep := st294_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p81 : ((983836335059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT294 (i+1))
      = (∑ i ∈ Finset.range 80, stT294 (i+1)) + stT294 81 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 80
    simpa using h
  have hprev := st294_p80
  have hstep := st294_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p82 : ((8339486754067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT294 (i+1))
      = (∑ i ∈ Finset.range 81, stT294 (i+1)) + stT294 82 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 81
    simpa using h
  have hprev := st294_p81
  have hstep := st294_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p83 : ((4160668613531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT294 (i+1))
      = (∑ i ∈ Finset.range 82, stT294 (i+1)) + stT294 83 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 82
    simpa using h
  have hprev := st294_p82
  have hstep := st294_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p84 : ((991730531399/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT294 (i+1))
      = (∑ i ∈ Finset.range 83, stT294 (i+1)) + stT294 84 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 83
    simpa using h
  have hprev := st294_p83
  have hstep := st294_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p85 : ((539566572687/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT294 (i+1))
      = (∑ i ∈ Finset.range 84, stT294 (i+1)) + stT294 85 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 84
    simpa using h
  have hprev := st294_p84
  have hstep := st294_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p86 : ((965862741643/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT294 (i+1))
      = (∑ i ∈ Finset.range 85, stT294 (i+1)) + stT294 86 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 85
    simpa using h
  have hprev := st294_p85
  have hstep := st294_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p87 : ((1093237956111/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT294 (i+1))
      = (∑ i ∈ Finset.range 86, stT294 (i+1)) + stT294 87 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 86
    simpa using h
  have hprev := st294_p86
  have hstep := st294_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p88 : ((1921209078353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT294 (i+1))
      = (∑ i ∈ Finset.range 87, stT294 (i+1)) + stT294 88 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 87
    simpa using h
  have hprev := st294_p87
  have hstep := st294_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p89 : ((8741065024077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT294 (i+1))
      = (∑ i ∈ Finset.range 88, stT294 (i+1)) + stT294 89 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 88
    simpa using h
  have hprev := st294_p88
  have hstep := st294_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p90 : ((1928447828069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT294 (i+1))
      = (∑ i ∈ Finset.range 89, stT294 (i+1)) + stT294 90 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 89
    simpa using h
  have hprev := st294_p89
  have hstep := st294_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p91 : ((2176047267449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT294 (i+1))
      = (∑ i ∈ Finset.range 90, stT294 (i+1)) + stT294 91 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 90
    simpa using h
  have hprev := st294_p90
  have hstep := st294_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p92 : ((7564357267/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT294 (i+1))
      = (∑ i ∈ Finset.range 91, stT294 (i+1)) + stT294 92 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 91
    simpa using h
  have hprev := st294_p91
  have hstep := st294_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p93 : ((2170781797459/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT294 (i+1))
      = (∑ i ∈ Finset.range 92, stT294 (i+1)) + stT294 93 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 92
    simpa using h
  have hprev := st294_p92
  have hstep := st294_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p94 : ((1937985726371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT294 (i+1))
      = (∑ i ∈ Finset.range 93, stT294 (i+1)) + stT294 94 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 93
    simpa using h
  have hprev := st294_p93
  have hstep := st294_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p95 : ((135797164327/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT294 (i+1))
      = (∑ i ∈ Finset.range 94, stT294 (i+1)) + stT294 95 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 94
    simpa using h
  have hprev := st294_p94
  have hstep := st294_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p96 : ((7732617634951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT294 (i+1))
      = (∑ i ∈ Finset.range 95, stT294 (i+1)) + stT294 96 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 95
    simpa using h
  have hprev := st294_p95
  have hstep := st294_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p97 : ((8714685669801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT294 (i+1))
      = (∑ i ∈ Finset.range 96, stT294 (i+1)) + stT294 97 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 96
    simpa using h
  have hprev := st294_p96
  have hstep := st294_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p98 : ((964122067341/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT294 (i+1))
      = (∑ i ∈ Finset.range 97, stT294 (i+1)) + stT294 98 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 97
    simpa using h
  have hprev := st294_p97
  have hstep := st294_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p99 : ((8717556246893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT294 (i+1))
      = (∑ i ∈ Finset.range 98, stT294 (i+1)) + stT294 99 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 98
    simpa using h
  have hprev := st294_p98
  have hstep := st294_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p100 : ((7740147246893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT294 (i+1))
      = (∑ i ∈ Finset.range 99, stT294 (i+1)) + stT294 100 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 99
    simpa using h
  have hprev := st294_p99
  have hstep := st294_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p101 : ((4322332367983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT294 (i+1))
      = (∑ i ∈ Finset.range 100, stT294 (i+1)) + stT294 101 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 100
    simpa using h
  have hprev := st294_p100
  have hstep := st294_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p102 : ((3935659275949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT294 (i+1))
      = (∑ i ∈ Finset.range 101, stT294 (i+1)) + stT294 102 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 101
    simpa using h
  have hprev := st294_p101
  have hstep := st294_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p103 : ((263938481179/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT294 (i+1))
      = (∑ i ∈ Finset.range 102, stT294 (i+1)) + stT294 103 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 102
    simpa using h
  have hprev := st294_p102
  have hstep := st294_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p104 : ((8135727520859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT294 (i+1))
      = (∑ i ∈ Finset.range 103, stT294 (i+1)) + stT294 104 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 103
    simpa using h
  have hprev := st294_p103
  have hstep := st294_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p105 : ((8129499320677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT294 (i+1))
      = (∑ i ∈ Finset.range 104, stT294 (i+1)) + stT294 105 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 104
    simpa using h
  have hprev := st294_p104
  have hstep := st294_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p106 : ((8472594091507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT294 (i+1))
      = (∑ i ∈ Finset.range 105, stT294 (i+1)) + stT294 106 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 105
    simpa using h
  have hprev := st294_p105
  have hstep := st294_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p107 : ((7819120482461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT294 (i+1))
      = (∑ i ∈ Finset.range 106, stT294 (i+1)) + stT294 107 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 106
    simpa using h
  have hprev := st294_p106
  have hstep := st294_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p108 : ((8696864725211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT294 (i+1))
      = (∑ i ∈ Finset.range 107, stT294 (i+1)) + stT294 108 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 107
    simpa using h
  have hprev := st294_p107
  have hstep := st294_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p109 : ((3869494438017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT294 (i+1))
      = (∑ i ∈ Finset.range 108, stT294 (i+1)) + stT294 109 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 108
    simpa using h
  have hprev := st294_p108
  have hstep := st294_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p110 : ((1073805831361/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT294 (i+1))
      = (∑ i ∈ Finset.range 109, stT294 (i+1)) + stT294 110 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 109
    simpa using h
  have hprev := st294_p109
  have hstep := st294_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p111 : ((2009076832253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT294 (i+1))
      = (∑ i ∈ Finset.range 110, stT294 (i+1)) + stT294 111 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 110
    simpa using h
  have hprev := st294_p110
  have hstep := st294_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p112 : ((8147906042667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT294 (i+1))
      = (∑ i ∈ Finset.range 111, stT294 (i+1)) + stT294 112 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 111
    simpa using h
  have hprev := st294_p111
  have hstep := st294_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p113 : ((8522572241387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT294 (i+1))
      = (∑ i ∈ Finset.range 112, stT294 (i+1)) + stT294 113 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 112
    simpa using h
  have hprev := st294_p112
  have hstep := st294_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p114 : ((1550937384293/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT294 (i+1))
      = (∑ i ∈ Finset.range 113, stT294 (i+1)) + stT294 114 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 113
    simpa using h
  have hprev := st294_p113
  have hstep := st294_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p115 : ((8686497138489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT294 (i+1))
      = (∑ i ∈ Finset.range 114, stT294 (i+1)) + stT294 115 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 114
    simpa using h
  have hprev := st294_p114
  have hstep := st294_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p116 : ((1579974199519/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT294 (i+1))
      = (∑ i ∈ Finset.range 115, stT294 (i+1)) + stT294 116 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 115
    simpa using h
  have hprev := st294_p115
  have hstep := st294_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p117 : ((1650695306219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT294 (i+1))
      = (∑ i ∈ Finset.range 116, stT294 (i+1)) + stT294 117 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 116
    simpa using h
  have hprev := st294_p116
  have hstep := st294_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p118 : ((8478333174613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT294 (i+1))
      = (∑ i ∈ Finset.range 117, stT294 (i+1)) + stT294 118 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 117
    simpa using h
  have hprev := st294_p117
  have hstep := st294_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p119 : ((484746621559/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT294 (i+1))
      = (∑ i ∈ Finset.range 118, stT294 (i+1)) + stT294 119 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 118
    simpa using h
  have hprev := st294_p118
  have hstep := st294_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p120 : ((4334288842937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT294 (i+1))
      = (∑ i ∈ Finset.range 119, stT294 (i+1)) + stT294 120 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 119
    simpa using h
  have hprev := st294_p119
  have hstep := st294_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p121 : ((7984849435683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT294 (i+1))
      = (∑ i ∈ Finset.range 120, stT294 (i+1)) + stT294 121 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 120
    simpa using h
  have hprev := st294_p120
  have hstep := st294_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p122 : ((4050732877391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT294 (i+1))
      = (∑ i ∈ Finset.range 121, stT294 (i+1)) + stT294 122 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 121
    simpa using h
  have hprev := st294_p121
  have hstep := st294_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p123 : ((4309811234499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT294 (i+1))
      = (∑ i ∈ Finset.range 122, stT294 (i+1)) + stT294 123 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 122
    simpa using h
  have hprev := st294_p122
  have hstep := st294_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p124 : ((7738957024989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT294 (i+1))
      = (∑ i ∈ Finset.range 123, stT294 (i+1)) + stT294 124 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 123
    simpa using h
  have hprev := st294_p123
  have hstep := st294_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p125 : ((8485715916143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT294 (i+1))
      = (∑ i ∈ Finset.range 124, stT294 (i+1)) + stT294 125 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 124
    simpa using h
  have hprev := st294_p124
  have hstep := st294_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p126 : ((4159041696343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT294 (i+1))
      = (∑ i ∈ Finset.range 125, stT294 (i+1)) + stT294 126 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 125
    simpa using h
  have hprev := st294_p125
  have hstep := st294_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p127 : ((974554104137/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT294 (i+1))
      = (∑ i ∈ Finset.range 126, stT294 (i+1)) + stT294 127 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 126
    simpa using h
  have hprev := st294_p126
  have hstep := st294_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p128 : ((4337595539731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT294 (i+1))
      = (∑ i ∈ Finset.range 127, stT294 (i+1)) + stT294 128 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 127
    simpa using h
  have hprev := st294_p127
  have hstep := st294_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p129 : ((802898230711/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT294 (i+1))
      = (∑ i ∈ Finset.range 128, stT294 (i+1)) + stT294 129 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 128
    simpa using h
  have hprev := st294_p128
  have hstep := st294_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p130 : ((3993690822311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT294 (i+1))
      = (∑ i ∈ Finset.range 129, stT294 (i+1)) + stT294 130 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 129
    simpa using h
  have hprev := st294_p129
  have hstep := st294_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p131 : ((869081995651/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT294 (i+1))
      = (∑ i ∈ Finset.range 130, stT294 (i+1)) + stT294 131 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 130
    simpa using h
  have hprev := st294_p130
  have hstep := st294_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p132 : ((7852131394279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT294 (i+1))
      = (∑ i ∈ Finset.range 131, stT294 (i+1)) + stT294 132 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 131
    simpa using h
  have hprev := st294_p131
  have hstep := st294_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p133 : ((510702857223/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT294 (i+1))
      = (∑ i ∈ Finset.range 132, stT294 (i+1)) + stT294 133 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 132
    simpa using h
  have hprev := st294_p132
  have hstep := st294_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p134 : ((431587780257/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT294 (i+1))
      = (∑ i ∈ Finset.range 133, stT294 (i+1)) + stT294 134 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 133
    simpa using h
  have hprev := st294_p133
  have hstep := st294_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p135 : ((777220286041/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT294 (i+1))
      = (∑ i ∈ Finset.range 134, stT294 (i+1)) + stT294 135 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 134
    simpa using h
  have hprev := st294_p134
  have hstep := st294_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p136 : ((4146102008271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT294 (i+1))
      = (∑ i ∈ Finset.range 135, stT294 (i+1)) + stT294 136 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 135
    simpa using h
  have hprev := st294_p135
  have hstep := st294_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p137 : ((8573845364663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT294 (i+1))
      = (∑ i ∈ Finset.range 136, stT294 (i+1)) + stT294 137 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 136
    simpa using h
  have hprev := st294_p136
  have hstep := st294_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p138 : ((3872589937093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT294 (i+1))
      = (∑ i ∈ Finset.range 137, stT294 (i+1)) + stT294 138 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 137
    simpa using h
  have hprev := st294_p137
  have hstep := st294_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p139 : ((4171799704631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT294 (i+1))
      = (∑ i ∈ Finset.range 138, stT294 (i+1)) + stT294 139 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 138
    simpa using h
  have hprev := st294_p138
  have hstep := st294_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p140 : ((427661021021/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT294 (i+1))
      = (∑ i ∈ Finset.range 139, stT294 (i+1)) + stT294 140 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 139
    simpa using h
  have hprev := st294_p139
  have hstep := st294_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p141 : ((1935428372387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT294 (i+1))
      = (∑ i ∈ Finset.range 140, stT294 (i+1)) + stT294 141 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 140
    simpa using h
  have hprev := st294_p140
  have hstep := st294_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p142 : ((8330574349877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT294 (i+1))
      = (∑ i ∈ Finset.range 141, stT294 (i+1)) + stT294 142 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 141
    simpa using h
  have hprev := st294_p141
  have hstep := st294_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p143 : ((8578004141563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT294 (i+1))
      = (∑ i ∈ Finset.range 142, stT294 (i+1)) + stT294 143 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 142
    simpa using h
  have hprev := st294_p142
  have hstep := st294_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p144 : ((7757678485303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT294 (i+1))
      = (∑ i ∈ Finset.range 143, stT294 (i+1)) + stT294 144 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 143
    simpa using h
  have hprev := st294_p143
  have hstep := st294_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p145 : ((8254416206311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT294 (i+1))
      = (∑ i ∈ Finset.range 144, stT294 (i+1)) + stT294 145 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 144
    simpa using h
  have hprev := st294_p144
  have hstep := st294_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p146 : ((8636241704321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT294 (i+1))
      = (∑ i ∈ Finset.range 145, stT294 (i+1)) + stT294 146 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 145
    simpa using h
  have hprev := st294_p145
  have hstep := st294_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p147 : ((3906078299029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT294 (i+1))
      = (∑ i ∈ Finset.range 146, stT294 (i+1)) + stT294 147 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 146
    simpa using h
  have hprev := st294_p146
  have hstep := st294_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p148 : ((2029015438439/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT294 (i+1))
      = (∑ i ∈ Finset.range 147, stT294 (i+1)) + stT294 148 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 147
    simpa using h
  have hprev := st294_p147
  have hstep := st294_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p149 : ((8693846535743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT294 (i+1))
      = (∑ i ∈ Finset.range 148, stT294 (i+1)) + stT294 149 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 148
    simpa using h
  have hprev := st294_p148
  have hstep := st294_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p150 : ((1587543611587/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT294 (i+1))
      = (∑ i ∈ Finset.range 149, stT294 (i+1)) + stT294 150 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 149
    simpa using h
  have hprev := st294_p149
  have hstep := st294_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p151 : ((1983493860581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT294 (i+1))
      = (∑ i ∈ Finset.range 150, stT294 (i+1)) + stT294 151 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 150
    simpa using h
  have hprev := st294_p150
  have hstep := st294_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p152 : ((1738295762803/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT294 (i+1))
      = (∑ i ∈ Finset.range 151, stT294 (i+1)) + stT294 152 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 151
    simpa using h
  have hprev := st294_p151
  have hstep := st294_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p153 : ((2039216455657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT294 (i+1))
      = (∑ i ∈ Finset.range 152, stT294 (i+1)) + stT294 153 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 152
    simpa using h
  have hprev := st294_p152
  have hstep := st294_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p154 : ((1941927833221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT294 (i+1))
      = (∑ i ∈ Finset.range 153, stT294 (i+1)) + stT294 154 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 153
    simpa using h
  have hprev := st294_p153
  have hstep := st294_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p155 : ((8559030643399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT294 (i+1))
      = (∑ i ∈ Finset.range 154, stT294 (i+1)) + stT294 155 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 154
    simpa using h
  have hprev := st294_p154
  have hstep := st294_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p156 : ((4220393988657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT294 (i+1))
      = (∑ i ∈ Finset.range 155, stT294 (i+1)) + stT294 156 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 155
    simpa using h
  have hprev := st294_p155
  have hstep := st294_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p157 : ((772414415949/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT294 (i+1))
      = (∑ i ∈ Finset.range 156, stT294 (i+1)) + stT294 157 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 156
    simpa using h
  have hprev := st294_p156
  have hstep := st294_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p158 : ((129178022487/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT294 (i+1))
      = (∑ i ∈ Finset.range 157, stT294 (i+1)) + stT294 158 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 157
    simpa using h
  have hprev := st294_p157
  have hstep := st294_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p159 : ((8671567916063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT294 (i+1))
      = (∑ i ∈ Finset.range 158, stT294 (i+1)) + stT294 159 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 158
    simpa using h
  have hprev := st294_p158
  have hstep := st294_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p160 : ((7907984813583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT294 (i+1))
      = (∑ i ∈ Finset.range 159, stT294 (i+1)) + stT294 160 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 159
    simpa using h
  have hprev := st294_p159
  have hstep := st294_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p161 : ((7906761665311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT294 (i+1))
      = (∑ i ∈ Finset.range 160, stT294 (i+1)) + stT294 161 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 160
    simpa using h
  have hprev := st294_p160
  have hstep := st294_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p162 : ((1733656180771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT294 (i+1))
      = (∑ i ∈ Finset.range 161, stT294 (i+1)) + stT294 162 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 161
    simpa using h
  have hprev := st294_p161
  have hstep := st294_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p163 : ((8301896472407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT294 (i+1))
      = (∑ i ∈ Finset.range 162, stT294 (i+1)) + stT294 163 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 162
    simpa using h
  have hprev := st294_p162
  have hstep := st294_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p164 : ((1542337201837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT294 (i+1))
      = (∑ i ∈ Finset.range 163, stT294 (i+1)) + stT294 164 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 163
    simpa using h
  have hprev := st294_p163
  have hstep := st294_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p165 : ((8335875585111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT294 (i+1))
      = (∑ i ∈ Finset.range 164, stT294 (i+1)) + stT294 165 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 164
    simpa using h
  have hprev := st294_p164
  have hstep := st294_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p166 : ((8662671990311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT294 (i+1))
      = (∑ i ∈ Finset.range 165, stT294 (i+1)) + stT294 166 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 165
    simpa using h
  have hprev := st294_p165
  have hstep := st294_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p167 : ((7910897331367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT294 (i+1))
      = (∑ i ∈ Finset.range 166, stT294 (i+1)) + stT294 167 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 166
    simpa using h
  have hprev := st294_p166
  have hstep := st294_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p168 : ((7868176892043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT294 (i+1))
      = (∑ i ∈ Finset.range 167, stT294 (i+1)) + stT294 168 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 167
    simpa using h
  have hprev := st294_p167
  have hstep := st294_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p169 : ((8631913820613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT294 (i+1))
      = (∑ i ∈ Finset.range 168, stT294 (i+1)) + stT294 169 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 168
    simpa using h
  have hprev := st294_p168
  have hstep := st294_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p170 : ((1052259634491/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT294 (i+1))
      = (∑ i ∈ Finset.range 169, stT294 (i+1)) + stT294 170 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 169
    simpa using h
  have hprev := st294_p169
  have hstep := st294_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p171 : ((965602424401/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT294 (i+1))
      = (∑ i ∈ Finset.range 170, stT294 (i+1)) + stT294 171 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 170
    simpa using h
  have hprev := st294_p170
  have hstep := st294_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p172 : ((31805766173/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT294 (i+1))
      = (∑ i ∈ Finset.range 171, stT294 (i+1)) + stT294 172 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 171
    simpa using h
  have hprev := st294_p171
  have hstep := st294_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p173 : ((4358633000329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT294 (i+1))
      = (∑ i ∈ Finset.range 172, stT294 (i+1)) + stT294 173 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 172
    simpa using h
  have hprev := st294_p172
  have hstep := st294_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p174 : ((8154317603337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT294 (i+1))
      = (∑ i ∈ Finset.range 173, stT294 (i+1)) + stT294 174 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 173
    simpa using h
  have hprev := st294_p173
  have hstep := st294_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p175 : ((241094352877/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT294 (i+1))
      = (∑ i ∈ Finset.range 174, stT294 (i+1)) + stT294 175 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 174
    simpa using h
  have hprev := st294_p174
  have hstep := st294_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p176 : ((4185366517799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT294 (i+1))
      = (∑ i ∈ Finset.range 175, stT294 (i+1)) + stT294 176 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 175
    simpa using h
  have hprev := st294_p175
  have hstep := st294_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p177 : ((1084698406697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT294 (i+1))
      = (∑ i ∈ Finset.range 176, stT294 (i+1)) + stT294 177 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 176
    simpa using h
  have hprev := st294_p176
  have hstep := st294_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p178 : ((12452610577/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT294 (i+1))
      = (∑ i ∈ Finset.range 177, stT294 (i+1)) + stT294 178 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 177
    simpa using h
  have hprev := st294_p177
  have hstep := st294_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p179 : ((1944574874537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT294 (i+1))
      = (∑ i ∈ Finset.range 178, stT294 (i+1)) + stT294 179 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 178
    simpa using h
  have hprev := st294_p178
  have hstep := st294_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p180 : ((4254960293459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT294 (i+1))
      = (∑ i ∈ Finset.range 179, stT294 (i+1)) + stT294 180 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 179
    simpa using h
  have hprev := st294_p179
  have hstep := st294_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p181 : ((269029420947/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT294 (i+1))
      = (∑ i ∈ Finset.range 180, stT294 (i+1)) + stT294 181 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 180
    simpa using h
  have hprev := st294_p180
  have hstep := st294_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p182 : ((983784248163/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT294 (i+1))
      = (∑ i ∈ Finset.range 181, stT294 (i+1)) + stT294 182 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 181
    simpa using h
  have hprev := st294_p181
  have hstep := st294_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p183 : ((979663085513/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT294 (i+1))
      = (∑ i ∈ Finset.range 182, stT294 (i+1)) + stT294 183 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 182
    simpa using h
  have hprev := st294_p182
  have hstep := st294_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p184 : ((857437656323/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT294 (i+1))
      = (∑ i ∈ Finset.range 183, stT294 (i+1)) + stT294 184 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 183
    simpa using h
  have hprev := st294_p183
  have hstep := st294_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p185 : ((856725674117/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT294 (i+1))
      = (∑ i ∈ Finset.range 184, stT294 (i+1)) + stT294 185 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 184
    simpa using h
  have hprev := st294_p184
  have hstep := st294_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p186 : ((156683054473/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT294 (i+1))
      = (∑ i ∈ Finset.range 185, stT294 (i+1)) + stT294 186 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 185
    simpa using h
  have hprev := st294_p185
  have hstep := st294_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p187 : ((3927756955021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT294 (i+1))
      = (∑ i ∈ Finset.range 186, stT294 (i+1)) + stT294 187 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 186
    simpa using h
  have hprev := st294_p186
  have hstep := st294_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p188 : ((4292254492459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT294 (i+1))
      = (∑ i ∈ Finset.range 187, stT294 (i+1)) + stT294 188 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 187
    simpa using h
  have hprev := st294_p187
  have hstep := st294_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p189 : ((1714645278419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT294 (i+1))
      = (∑ i ∈ Finset.range 188, stT294 (i+1)) + stT294 189 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 188
    simpa using h
  have hprev := st294_p188
  have hstep := st294_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p190 : ((7847682648211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT294 (i+1))
      = (∑ i ∈ Finset.range 189, stT294 (i+1)) + stT294 190 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 189
    simpa using h
  have hprev := st294_p189
  have hstep := st294_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p191 : ((7824879905661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT294 (i+1))
      = (∑ i ∈ Finset.range 190, stT294 (i+1)) + stT294 191 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 190
    simpa using h
  have hprev := st294_p190
  have hstep := st294_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p192 : ((8544876714707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT294 (i+1))
      = (∑ i ∈ Finset.range 191, stT294 (i+1)) + stT294 192 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 191
    simpa using h
  have hprev := st294_p191
  have hstep := st294_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p193 : ((4312091885981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT294 (i+1))
      = (∑ i ∈ Finset.range 192, stT294 (i+1)) + stT294 193 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 192
    simpa using h
  have hprev := st294_p192
  have hstep := st294_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p194 : ((989442805483/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT294 (i+1))
      = (∑ i ∈ Finset.range 193, stT294 (i+1)) + stT294 194 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 193
    simpa using h
  have hprev := st294_p193
  have hstep := st294_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p195 : ((7758403181069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT294 (i+1))
      = (∑ i ∈ Finset.range 194, stT294 (i+1)) + stT294 195 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 194
    simpa using h
  have hprev := st294_p194
  have hstep := st294_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p196 : ((4221590176717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT294 (i+1))
      = (∑ i ∈ Finset.range 195, stT294 (i+1)) + stT294 196 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 195
    simpa using h
  have hprev := st294_p195
  have hstep := st294_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p197 : ((543492851579/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT294 (i+1))
      = (∑ i ∈ Finset.range 196, stT294 (i+1)) + stT294 197 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 196
    simpa using h
  have hprev := st294_p196
  have hstep := st294_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p198 : ((4027158811357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT294 (i+1))
      = (∑ i ∈ Finset.range 197, stT294 (i+1)) + stT294 198 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 197
    simpa using h
  have hprev := st294_p197
  have hstep := st294_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p199 : ((961637375239/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT294 (i+1))
      = (∑ i ∈ Finset.range 198, stT294 (i+1)) + stT294 199 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 198
    simpa using h
  have hprev := st294_p198
  have hstep := st294_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p200 : ((4131844498117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT294 (i+1))
      = (∑ i ∈ Finset.range 199, stT294 (i+1)) + stT294 200 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 199
    simpa using h
  have hprev := st294_p199
  have hstep := st294_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p201 : ((273037493467/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT294 (i+1))
      = (∑ i ∈ Finset.range 200, stT294 (i+1)) + stT294 201 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 200
    simpa using h
  have hprev := st294_p200
  have hstep := st294_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p202 : ((4135824699343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT294 (i+1))
      = (∑ i ∈ Finset.range 201, stT294 (i+1)) + stT294 202 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 201
    simpa using h
  have hprev := st294_p201
  have hstep := st294_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p203 : ((3846943503447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT294 (i+1))
      = (∑ i ∈ Finset.range 202, stT294 (i+1)) + stT294 203 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 202
    simpa using h
  have hprev := st294_p202
  have hstep := st294_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p204 : ((4007909890287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT294 (i+1))
      = (∑ i ∈ Finset.range 203, stT294 (i+1)) + stT294 204 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 203
    simpa using h
  have hprev := st294_p203
  have hstep := st294_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p205 : ((2168270555271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT294 (i+1))
      = (∑ i ∈ Finset.range 204, stT294 (i+1)) + stT294 205 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 204
    simpa using h
  have hprev := st294_p204
  have hstep := st294_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p206 : ((170628710043/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT294 (i+1))
      = (∑ i ∈ Finset.range 205, stT294 (i+1)) + stT294 206 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 205
    simpa using h
  have hprev := st294_p205
  have hstep := st294_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p207 : ((3918733999197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT294 (i+1))
      = (∑ i ∈ Finset.range 206, stT294 (i+1)) + stT294 207 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 206
    simpa using h
  have hprev := st294_p206
  have hstep := st294_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p208 : ((155413654309/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT294 (i+1))
      = (∑ i ∈ Finset.range 207, stT294 (i+1)) + stT294 208 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 207
    simpa using h
  have hprev := st294_p207
  have hstep := st294_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p209 : ((4219797527577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT294 (i+1))
      = (∑ i ∈ Finset.range 208, stT294 (i+1)) + stT294 209 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 208
    simpa using h
  have hprev := st294_p208
  have hstep := st294_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p210 : ((272617403797/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT294 (i+1))
      = (∑ i ∈ Finset.range 209, stT294 (i+1)) + stT294 210 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 209
    simpa using h
  have hprev := st294_p209
  have hstep := st294_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p211 : ((8154977570133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT294 (i+1))
      = (∑ i ∈ Finset.range 210, stT294 (i+1)) + stT294 211 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 210
    simpa using h
  have hprev := st294_p210
  have hstep := st294_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p212 : ((7672196269313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT294 (i+1))
      = (∑ i ∈ Finset.range 211, stT294 (i+1)) + stT294 212 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 211
    simpa using h
  have hprev := st294_p211
  have hstep := st294_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p213 : ((8061359071733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT294 (i+1))
      = (∑ i ∈ Finset.range 212, stT294 (i+1)) + stT294 213 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 212
    simpa using h
  have hprev := st294_p212
  have hstep := st294_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p214 : ((8688105346153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT294 (i+1))
      = (∑ i ∈ Finset.range 213, stT294 (i+1)) + stT294 214 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 213
    simpa using h
  have hprev := st294_p213
  have hstep := st294_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p215 : ((8545699334193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT294 (i+1))
      = (∑ i ∈ Finset.range 214, stT294 (i+1)) + stT294 215 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 214
    simpa using h
  have hprev := st294_p214
  have hstep := st294_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p216 : ((7865222055691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT294 (i+1))
      = (∑ i ∈ Finset.range 215, stT294 (i+1)) + stT294 216 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 215
    simpa using h
  have hprev := st294_p215
  have hstep := st294_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p217 : ((7724236810711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT294 (i+1))
      = (∑ i ∈ Finset.range 216, stT294 (i+1)) + stT294 217 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 216
    simpa using h
  have hprev := st294_p216
  have hstep := st294_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p218 : ((8340311501551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT294 (i+1))
      = (∑ i ∈ Finset.range 217, stT294 (i+1)) + stT294 218 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 217
    simpa using h
  have hprev := st294_p217
  have hstep := st294_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p219 : ((8751029856047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT294 (i+1))
      = (∑ i ∈ Finset.range 218, stT294 (i+1)) + stT294 219 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 218
    simpa using h
  have hprev := st294_p218
  have hstep := st294_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p220 : ((8323901907447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT294 (i+1))
      = (∑ i ∈ Finset.range 219, stT294 (i+1)) + stT294 220 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 219
    simpa using h
  have hprev := st294_p219
  have hstep := st294_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p221 : ((1543539952523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT294 (i+1))
      = (∑ i ∈ Finset.range 220, stT294 (i+1)) + stT294 221 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 220
    simpa using h
  have hprev := st294_p220
  have hstep := st294_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p222 : ((7854277995147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT294 (i+1))
      = (∑ i ∈ Finset.range 221, stT294 (i+1)) + stT294 222 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 221
    simpa using h
  have hprev := st294_p221
  have hstep := st294_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p223 : ((8523199756333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT294 (i+1))
      = (∑ i ∈ Finset.range 222, stT294 (i+1)) + stT294 223 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 222
    simpa using h
  have hprev := st294_p222
  have hstep := st294_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p224 : ((545027198823/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT294 (i+1))
      = (∑ i ∈ Finset.range 223, stT294 (i+1)) + stT294 224 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 223
    simpa using h
  have hprev := st294_p223
  have hstep := st294_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p225 : ((8155874232221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT294 (i+1))
      = (∑ i ∈ Finset.range 224, stT294 (i+1)) + stT294 225 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 224
    simpa using h
  have hprev := st294_p224
  have hstep := st294_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p226 : ((7665838665577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT294 (i+1))
      = (∑ i ∈ Finset.range 225, stT294 (i+1)) + stT294 226 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 225
    simpa using h
  have hprev := st294_p225
  have hstep := st294_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p227 : ((3983187215573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT294 (i+1))
      = (∑ i ∈ Finset.range 226, stT294 (i+1)) + stT294 227 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 226
    simpa using h
  have hprev := st294_p226
  have hstep := st294_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p228 : ((861646400847/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT294 (i+1))
      = (∑ i ∈ Finset.range 227, stT294 (i+1)) + stT294 228 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 227
    simpa using h
  have hprev := st294_p227
  have hstep := st294_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p229 : ((542344109349/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT294 (i+1))
      = (∑ i ∈ Finset.range 228, stT294 (i+1)) + stT294 229 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 228
    simpa using h
  have hprev := st294_p228
  have hstep := st294_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p230 : ((63013078377/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT294 (i+1))
      = (∑ i ∈ Finset.range 229, stT294 (i+1)) + stT294 230 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 229
    simpa using h
  have hprev := st294_p229
  have hstep := st294_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p231 : ((119579522497/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT294 (i+1))
      = (∑ i ∈ Finset.range 230, stT294 (i+1)) + stT294 231 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 230
    simpa using h
  have hprev := st294_p230
  have hstep := st294_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p232 : ((400977328139/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT294 (i+1))
      = (∑ i ∈ Finset.range 231, stT294 (i+1)) + stT294 232 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 231
    simpa using h
  have hprev := st294_p231
  have hstep := st294_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p233 : ((2161996448673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT294 (i+1))
      = (∑ i ∈ Finset.range 232, stT294 (i+1)) + stT294 233 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 232
    simpa using h
  have hprev := st294_p232
  have hstep := st294_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p234 : ((2166172575463/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT294 (i+1))
      = (∑ i ∈ Finset.range 233, stT294 (i+1)) + stT294 234 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 233
    simpa using h
  have hprev := st294_p233
  have hstep := st294_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p235 : ((8050232261947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT294 (i+1))
      = (∑ i ∈ Finset.range 234, stT294 (i+1)) + stT294 235 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 234
    simpa using h
  have hprev := st294_p234
  have hstep := st294_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p236 : ((7648442970147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT294 (i+1))
      = (∑ i ∈ Finset.range 235, stT294 (i+1)) + stT294 236 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 235
    simpa using h
  have hprev := st294_p235
  have hstep := st294_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p237 : ((2000819944983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT294 (i+1))
      = (∑ i ∈ Finset.range 236, stT294 (i+1)) + stT294 237 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 236
    simpa using h
  have hprev := st294_p236
  have hstep := st294_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p238 : ((1726408764033/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT294 (i+1))
      = (∑ i ∈ Finset.range 237, stT294 (i+1)) + stT294 238 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 237
    simpa using h
  have hprev := st294_p237
  have hstep := st294_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p239 : ((8692032965051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT294 (i+1))
      = (∑ i ∈ Finset.range 238, stT294 (i+1)) + stT294 239 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 238
    simpa using h
  have hprev := st294_p238
  have hstep := st294_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p240 : ((324276542279/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT294 (i+1))
      = (∑ i ∈ Finset.range 239, stT294 (i+1)) + stT294 240 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 239
    simpa using h
  have hprev := st294_p239
  have hstep := st294_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p241 : ((7651748355833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT294 (i+1))
      = (∑ i ∈ Finset.range 240, stT294 (i+1)) + stT294 241 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 240
    simpa using h
  have hprev := st294_p240
  have hstep := st294_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p242 : ((7921321100001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT294 (i+1))
      = (∑ i ∈ Finset.range 241, stT294 (i+1)) + stT294 242 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 241
    simpa using h
  have hprev := st294_p241
  have hstep := st294_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p243 : ((8560981278001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT294 (i+1))
      = (∑ i ∈ Finset.range 242, stT294 (i+1)) + stT294 243 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 242
    simpa using h
  have hprev := st294_p242
  have hstep := st294_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p244 : ((8743352414633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT294 (i+1))
      = (∑ i ∈ Finset.range 243, stT294 (i+1)) + stT294 244 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 243
    simpa using h
  have hprev := st294_p243
  have hstep := st294_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p245 : ((4118768122027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT294 (i+1))
      = (∑ i ∈ Finset.range 244, stT294 (i+1)) + stT294 245 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 244
    simpa using h
  have hprev := st294_p244
  have hstep := st294_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p246 : ((3845347051039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT294 (i+1))
      = (∑ i ∈ Finset.range 245, stT294 (i+1)) + stT294 246 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 245
    simpa using h
  have hprev := st294_p245
  have hstep := st294_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p247 : ((779334452723/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT294 (i+1))
      = (∑ i ∈ Finset.range 246, stT294 (i+1)) + stT294 247 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 246
    simpa using h
  have hprev := st294_p246
  have hstep := st294_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p248 : ((841286767223/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT294 (i+1))
      = (∑ i ∈ Finset.range 247, stT294 (i+1)) + stT294 248 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 247
    simpa using h
  have hprev := st294_p247
  have hstep := st294_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p249 : ((175501198999/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT294 (i+1))
      = (∑ i ∈ Finset.range 248, stT294 (i+1)) + stT294 249 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 248
    simpa using h
  have hprev := st294_p248
  have hstep := st294_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p250 : ((4216881013283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT294 (i+1))
      = (∑ i ∈ Finset.range 249, stT294 (i+1)) + stT294 250 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 249
    simpa using h
  have hprev := st294_p249
  have hstep := st294_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p251 : ((7811897982251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT294 (i+1))
      = (∑ i ∈ Finset.range 250, stT294 (i+1)) + stT294 251 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 250
    simpa using h
  have hprev := st294_p250
  have hstep := st294_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p252 : ((479299131003/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT294 (i+1))
      = (∑ i ∈ Finset.range 251, stT294 (i+1)) + stT294 252 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 251
    simpa using h
  have hprev := st294_p251
  have hstep := st294_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p253 : ((817467289617/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT294 (i+1))
      = (∑ i ∈ Finset.range 252, stT294 (i+1)) + stT294 253 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 252
    simpa using h
  have hprev := st294_p252
  have hstep := st294_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p254 : ((1743559463343/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT294 (i+1))
      = (∑ i ∈ Finset.range 253, stT294 (i+1)) + stT294 254 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 253
    simpa using h
  have hprev := st294_p253
  have hstep := st294_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p255 : ((108122718273/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT294 (i+1))
      = (∑ i ∈ Finset.range 254, stT294 (i+1)) + stT294 255 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 254
    simpa using h
  have hprev := st294_p254
  have hstep := st294_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p256 : ((8054820884847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT294 (i+1))
      = (∑ i ∈ Finset.range 255, stT294 (i+1)) + stT294 256 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 255
    simpa using h
  have hprev := st294_p255
  have hstep := st294_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p257 : ((477248277047/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT294 (i+1))
      = (∑ i ∈ Finset.range 256, stT294 (i+1)) + stT294 257 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 256
    simpa using h
  have hprev := st294_p256
  have hstep := st294_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p258 : ((985201960777/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT294 (i+1))
      = (∑ i ∈ Finset.range 257, stT294 (i+1)) + stT294 258 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 257
    simpa using h
  have hprev := st294_p257
  have hstep := st294_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p259 : ((8502683322251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT294 (i+1))
      = (∑ i ∈ Finset.range 258, stT294 (i+1)) + stT294 259 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 258
    simpa using h
  have hprev := st294_p258
  have hstep := st294_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p260 : ((4390525537083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT294 (i+1))
      = (∑ i ∈ Finset.range 259, stT294 (i+1)) + stT294 260 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 259
    simpa using h
  have hprev := st294_p259
  have hstep := st294_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p261 : ((2100001905519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT294 (i+1))
      = (∑ i ∈ Finset.range 260, stT294 (i+1)) + stT294 261 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 260
    simpa using h
  have hprev := st294_p260
  have hstep := st294_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p262 : ((7796565452811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT294 (i+1))
      = (∑ i ∈ Finset.range 261, stT294 (i+1)) + stT294 262 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 261
    simpa using h
  have hprev := st294_p261
  have hstep := st294_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p263 : ((7653345199283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT294 (i+1))
      = (∑ i ∈ Finset.range 262, stT294 (i+1)) + stT294 263 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 262
    simpa using h
  have hprev := st294_p262
  have hstep := st294_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p264 : ((1625642178989/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT294 (i+1))
      = (∑ i ∈ Finset.range 263, stT294 (i+1)) + stT294 264 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 263
    simpa using h
  have hprev := st294_p263
  have hstep := st294_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p265 : ((868850629297/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT294 (i+1))
      = (∑ i ∈ Finset.range 264, stT294 (i+1)) + stT294 265 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 264
    simpa using h
  have hprev := st294_p264
  have hstep := st294_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p266 : ((8713735123403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT294 (i+1))
      = (∑ i ∈ Finset.range 265, stT294 (i+1)) + stT294 266 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 265
    simpa using h
  have hprev := st294_p265
  have hstep := st294_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p267 : ((4089613845961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT294 (i+1))
      = (∑ i ∈ Finset.range 266, stT294 (i+1)) + stT294 267 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 266
    simpa using h
  have hprev := st294_p266
  have hstep := st294_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p268 : ((3835824827401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT294 (i+1))
      = (∑ i ∈ Finset.range 267, stT294 (i+1)) + stT294 268 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 267
    simpa using h
  have hprev := st294_p267
  have hstep := st294_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p269 : ((3870581345951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT294 (i+1))
      = (∑ i ∈ Finset.range 268, stT294 (i+1)) + stT294 269 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 268
    simpa using h
  have hprev := st294_p268
  have hstep := st294_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p270 : ((4154738910971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT294 (i+1))
      = (∑ i ∈ Finset.range 269, stT294 (i+1)) + stT294 270 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 269
    simpa using h
  have hprev := st294_p269
  have hstep := st294_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p271 : ((876555760911/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT294 (i+1))
      = (∑ i ∈ Finset.range 270, stT294 (i+1)) + stT294 271 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 270
    simpa using h
  have hprev := st294_p270
  have hstep := st294_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p272 : ((862523961899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT294 (i+1))
      = (∑ i ∈ Finset.range 271, stT294 (i+1)) + stT294 272 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 271
    simpa using h
  have hprev := st294_p271
  have hstep := st294_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p273 : ((4020027779947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT294 (i+1))
      = (∑ i ∈ Finset.range 272, stT294 (i+1)) + stT294 273 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 272
    simpa using h
  have hprev := st294_p272
  have hstep := st294_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p274 : ((7626310445007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT294 (i+1))
      = (∑ i ∈ Finset.range 273, stT294 (i+1)) + stT294 274 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 273
    simpa using h
  have hprev := st294_p273
  have hstep := st294_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p275 : ((7814064962839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT294 (i+1))
      = (∑ i ∈ Finset.range 274, stT294 (i+1)) + stT294 275 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 274
    simpa using h
  have hprev := st294_p274
  have hstep := st294_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p276 : ((4202724986273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT294 (i+1))
      = (∑ i ∈ Finset.range 275, stT294 (i+1)) + stT294 276 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 275
    simpa using h
  have hprev := st294_p275
  have hstep := st294_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p277 : ((34335473683/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT294 (i+1))
      = (∑ i ∈ Finset.range 276, stT294 (i+1)) + stT294 277 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 276
    simpa using h
  have hprev := st294_p276
  have hstep := st294_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p278 : ((8575702411421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT294 (i+1))
      = (∑ i ∈ Finset.range 277, stT294 (i+1)) + stT294 278 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 277
    simpa using h
  have hprev := st294_p277
  have hstep := st294_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p279 : ((7983689157061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT294 (i+1))
      = (∑ i ∈ Finset.range 278, stT294 (i+1)) + stT294 279 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 278
    simpa using h
  have hprev := st294_p278
  have hstep := st294_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p280 : ((1903247890159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT294 (i+1))
      = (∑ i ∈ Finset.range 279, stT294 (i+1)) + stT294 280 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 279
    simpa using h
  have hprev := st294_p279
  have hstep := st294_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p281 : ((3916857941867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT294 (i+1))
      = (∑ i ∈ Finset.range 280, stT294 (i+1)) + stT294 281 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 280
    simpa using h
  have hprev := st294_p280
  have hstep := st294_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p282 : ((8422701144559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT294 (i+1))
      = (∑ i ∈ Finset.range 281, stT294 (i+1)) + stT294 282 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 281
    simpa using h
  have hprev := st294_p281
  have hstep := st294_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p283 : ((8795202150631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT294 (i+1))
      = (∑ i ∈ Finset.range 282, stT294 (i+1)) + stT294 283 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 282
    simpa using h
  have hprev := st294_p282
  have hstep := st294_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p284 : ((8586279860569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT294 (i+1))
      = (∑ i ∈ Finset.range 283, stT294 (i+1)) + stT294 284 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 283
    simpa using h
  have hprev := st294_p283
  have hstep := st294_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p285 : ((8003202307117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT294 (i+1))
      = (∑ i ∈ Finset.range 284, stT294 (i+1)) + stT294 285 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 284
    simpa using h
  have hprev := st294_p284
  have hstep := st294_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p286 : ((380690277427/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT294 (i+1))
      = (∑ i ∈ Finset.range 285, stT294 (i+1)) + stT294 286 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 285
    simpa using h
  have hprev := st294_p285
  have hstep := st294_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p287 : ((7792381488627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT294 (i+1))
      = (∑ i ∈ Finset.range 286, stT294 (i+1)) + stT294 287 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 286
    simpa using h
  have hprev := st294_p286
  have hstep := st294_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p288 : ((8364582270417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT294 (i+1))
      = (∑ i ∈ Finset.range 287, stT294 (i+1)) + stT294 288 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 287
    simpa using h
  have hprev := st294_p287
  have hstep := st294_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p289 : ((1097926066449/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT294 (i+1))
      = (∑ i ∈ Finset.range 288, stT294 (i+1)) + stT294 289 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 288
    simpa using h
  have hprev := st294_p288
  have hstep := st294_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p290 : ((346137626773/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT294 (i+1))
      = (∑ i ∈ Finset.range 289, stT294 (i+1)) + stT294 290 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 289
    simpa using h
  have hprev := st294_p289
  have hstep := st294_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p291 : ((8099891001401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT294 (i+1))
      = (∑ i ∈ Finset.range 290, stT294 (i+1)) + stT294 291 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 290
    simpa using h
  have hprev := st294_p290
  have hstep := st294_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p292 : ((7642194366329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT294 (i+1))
      = (∑ i ∈ Finset.range 291, stT294 (i+1)) + stT294 292 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 291
    simpa using h
  have hprev := st294_p291
  have hstep := st294_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p293 : ((7704665850733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT294 (i+1))
      = (∑ i ∈ Finset.range 292, stT294 (i+1)) + stT294 293 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 292
    simpa using h
  have hprev := st294_p292
  have hstep := st294_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p294 : ((1028338783033/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT294 (i+1))
      = (∑ i ∈ Finset.range 293, stT294 (i+1)) + stT294 294 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 293
    simpa using h
  have hprev := st294_p293
  have hstep := st294_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p295 : ((4363546114417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT294 (i+1))
      = (∑ i ∈ Finset.range 294, stT294 (i+1)) + stT294 295 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 294
    simpa using h
  have hprev := st294_p294
  have hstep := st294_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p296 : ((4374974415973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT294 (i+1))
      = (∑ i ∈ Finset.range 295, stT294 (i+1)) + stT294 296 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 295
    simpa using h
  have hprev := st294_p295
  have hstep := st294_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p297 : ((1034647271203/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT294 (i+1))
      = (∑ i ∈ Finset.range 296, stT294 (i+1)) + stT294 297 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 296
    simpa using h
  have hprev := st294_p296
  have hstep := st294_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p298 : ((483559140449/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT294 (i+1))
      = (∑ i ∈ Finset.range 297, stT294 (i+1)) + stT294 298 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 297
    simpa using h
  have hprev := st294_p297
  have hstep := st294_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p299 : ((3806385803507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT294 (i+1))
      = (∑ i ∈ Finset.range 298, stT294 (i+1)) + stT294 299 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 298
    simpa using h
  have hprev := st294_p298
  have hstep := st294_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p300 : ((500793114229/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT294 (i+1))
      = (∑ i ∈ Finset.range 299, stT294 (i+1)) + stT294 300 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 299
    simpa using h
  have hprev := st294_p299
  have hstep := st294_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p301 : ((1072553382623/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT294 (i+1))
      = (∑ i ∈ Finset.range 300, stT294 (i+1)) + stT294 301 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 300
    simpa using h
  have hprev := st294_p300
  have hstep := st294_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p302 : ((8816450357759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT294 (i+1))
      = (∑ i ∈ Finset.range 301, stT294 (i+1)) + stT294 302 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 301
    simpa using h
  have hprev := st294_p301
  have hstep := st294_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p303 : ((2129132099831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT294 (i+1))
      = (∑ i ∈ Finset.range 302, stT294 (i+1)) + stT294 303 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 302
    simpa using h
  have hprev := st294_p302
  have hstep := st294_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p304 : ((496483410929/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT294 (i+1))
      = (∑ i ∈ Finset.range 303, stT294 (i+1)) + stT294 304 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 303
    simpa using h
  have hprev := st294_p303
  have hstep := st294_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p305 : ((3796702954743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT294 (i+1))
      = (∑ i ∈ Finset.range 304, stT294 (i+1)) + stT294 305 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 304
    simpa using h
  have hprev := st294_p304
  have hstep := st294_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p306 : ((7764548064683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT294 (i+1))
      = (∑ i ∈ Finset.range 305, stT294 (i+1)) + stT294 306 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 305
    simpa using h
  have hprev := st294_p305
  have hstep := st294_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p307 : ((8308458891253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT294 (i+1))
      = (∑ i ∈ Finset.range 306, stT294 (i+1)) + stT294 307 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 306
    simpa using h
  have hprev := st294_p306
  have hstep := st294_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p308 : ((1752496108733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT294 (i+1))
      = (∑ i ∈ Finset.range 307, stT294 (i+1)) + stT294 308 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 307
    simpa using h
  have hprev := st294_p307
  have hstep := st294_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p309 : ((349795174621/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT294 (i+1))
      = (∑ i ∈ Finset.range 308, stT294 (i+1)) + stT294 309 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 308
    simpa using h
  have hprev := st294_p308
  have hstep := st294_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p310 : ((1654578316857/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT294 (i+1))
      = (∑ i ∈ Finset.range 309, stT294 (i+1)) + stT294 310 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 309
    simpa using h
  have hprev := st294_p309
  have hstep := st294_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p311 : ((7741509769389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT294 (i+1))
      = (∑ i ∈ Finset.range 310, stT294 (i+1)) + stT294 311 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 310
    simpa using h
  have hprev := st294_p310
  have hstep := st294_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p312 : ((948795601233/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT294 (i+1))
      = (∑ i ∈ Finset.range 311, stT294 (i+1)) + stT294 312 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 311
    simpa using h
  have hprev := st294_p311
  have hstep := st294_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p313 : ((1985399583783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT294 (i+1))
      = (∑ i ∈ Finset.range 312, stT294 (i+1)) + stT294 313 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 312
    simpa using h
  have hprev := st294_p312
  have hstep := st294_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p314 : ((531592111909/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT294 (i+1))
      = (∑ i ∈ Finset.range 313, stT294 (i+1)) + stT294 314 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 313
    simpa using h
  have hprev := st294_p313
  have hstep := st294_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p315 : ((44113852601/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT294 (i+1))
      = (∑ i ∈ Finset.range 314, stT294 (i+1)) + stT294 315 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 314
    simpa using h
  have hprev := st294_p314
  have hstep := st294_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p316 : ((1079816959071/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT294 (i+1))
      = (∑ i ∈ Finset.range 315, stT294 (i+1)) + stT294 316 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 315
    simpa using h
  have hprev := st294_p315
  have hstep := st294_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p317 : ((1012914181319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT294 (i+1))
      = (∑ i ∈ Finset.range 316, stT294 (i+1)) + stT294 317 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 316
    simpa using h
  have hprev := st294_p316
  have hstep := st294_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p318 : ((238940189483/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT294 (i+1))
      = (∑ i ∈ Finset.range 317, stT294 (i+1)) + stT294 318 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 317
    simpa using h
  have hprev := st294_p317
  have hstep := st294_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p319 : ((3814600405181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT294 (i+1))
      = (∑ i ∈ Finset.range 318, stT294 (i+1)) + stT294 319 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 318
    simpa using h
  have hprev := st294_p318
  have hstep := st294_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p320 : ((4031787624453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT294 (i+1))
      = (∑ i ∈ Finset.range 319, stT294 (i+1)) + stT294 320 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 319
    simpa using h
  have hprev := st294_p319
  have hstep := st294_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p321 : ((8606109491401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT294 (i+1))
      = (∑ i ∈ Finset.range 320, stT294 (i+1)) + stT294 321 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 320
    simpa using h
  have hprev := st294_p320
  have hstep := st294_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p322 : ((8833135632153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT294 (i+1))
      = (∑ i ∈ Finset.range 321, stT294 (i+1)) + stT294 322 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 321
    simpa using h
  have hprev := st294_p321
  have hstep := st294_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p323 : ((2142566427907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT294 (i+1))
      = (∑ i ∈ Finset.range 322, stT294 (i+1)) + stT294 323 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 322
    simpa using h
  have hprev := st294_p322
  have hstep := st294_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p324 : ((1002833367527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT294 (i+1))
      = (∑ i ∈ Finset.range 323, stT294 (i+1)) + stT294 324 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 323
    simpa using h
  have hprev := st294_p323
  have hstep := st294_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p325 : ((7611468753019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT294 (i+1))
      = (∑ i ∈ Finset.range 324, stT294 (i+1)) + stT294 325 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 324
    simpa using h
  have hprev := st294_p324
  have hstep := st294_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p326 : ((305970134851/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT294 (i+1))
      = (∑ i ∈ Finset.range 325, stT294 (i+1)) + stT294 326 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 325
    simpa using h
  have hprev := st294_p325
  have hstep := st294_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p327 : ((8104996979403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT294 (i+1))
      = (∑ i ∈ Finset.range 326, stT294 (i+1)) + stT294 327 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 326
    simpa using h
  have hprev := st294_p326
  have hstep := st294_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p328 : ((8633123002449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT294 (i+1))
      = (∑ i ∈ Finset.range 327, stT294 (i+1)) + stT294 328 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 327
    simpa using h
  have hprev := st294_p327
  have hstep := st294_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p329 : ((8837593246141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT294 (i+1))
      = (∑ i ∈ Finset.range 328, stT294 (i+1)) + stT294 329 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 328
    simpa using h
  have hprev := st294_p328
  have hstep := st294_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p330 : ((8567748621187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT294 (i+1))
      = (∑ i ∈ Finset.range 329, stT294 (i+1)) + stT294 330 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 329
    simpa using h
  have hprev := st294_p329
  have hstep := st294_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p331 : ((8025877817637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT294 (i+1))
      = (∑ i ∈ Finset.range 330, stT294 (i+1)) + stT294 331 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 330
    simpa using h
  have hprev := st294_p330
  have hstep := st294_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p332 : ((7612434838021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT294 (i+1))
      = (∑ i ∈ Finset.range 331, stT294 (i+1)) + stT294 332 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 331
    simpa using h
  have hprev := st294_p331
  have hstep := st294_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p333 : ((1525900325089/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT294 (i+1))
      = (∑ i ∈ Finset.range 332, stT294 (i+1)) + stT294 333 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 332
    simpa using h
  have hprev := st294_p332
  have hstep := st294_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p334 : ((1612476980029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT294 (i+1))
      = (∑ i ∈ Finset.range 333, stT294 (i+1)) + stT294 334 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 333
    simpa using h
  have hprev := st294_p333
  have hstep := st294_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p335 : ((8595405755007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT294 (i+1))
      = (∑ i ∈ Finset.range 334, stT294 (i+1)) + stT294 335 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 334
    simpa using h
  have hprev := st294_p334
  have hstep := st294_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p336 : ((8844143814087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT294 (i+1))
      = (∑ i ∈ Finset.range 335, stT294 (i+1)) + stT294 336 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 335
    simpa using h
  have hprev := st294_p335
  have hstep := st294_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p337 : ((2157969367843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT294 (i+1))
      = (∑ i ∈ Finset.range 336, stT294 (i+1)) + stT294 337 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 336
    simpa using h
  have hprev := st294_p336
  have hstep := st294_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p338 : ((1014014268623/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT294 (i+1))
      = (∑ i ∈ Finset.range 337, stT294 (i+1)) + stT294 338 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 337
    simpa using h
  have hprev := st294_p337
  have hstep := st294_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p339 : ((3827257914791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT294 (i+1))
      = (∑ i ∈ Finset.range 338, stT294 (i+1)) + stT294 339 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 338
    simpa using h
  have hprev := st294_p338
  have hstep := st294_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p340 : ((1895260613069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT294 (i+1))
      = (∑ i ∈ Finset.range 339, stT294 (i+1)) + stT294 340 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 339
    simpa using h
  have hprev := st294_p339
  have hstep := st294_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p341 : ((3970579138843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT294 (i+1))
      = (∑ i ∈ Finset.range 340, stT294 (i+1)) + stT294 341 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 340
    simpa using h
  have hprev := st294_p340
  have hstep := st294_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p342 : ((424087865401/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT294 (i+1))
      = (∑ i ∈ Finset.range 341, stT294 (i+1)) + stT294 342 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 341
    simpa using h
  have hprev := st294_p341
  have hstep := st294_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p343 : ((4413668273449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT294 (i+1))
      = (∑ i ∈ Finset.range 342, stT294 (i+1)) + stT294 343 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 342
    simpa using h
  have hprev := st294_p342
  have hstep := st294_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p344 : ((4370363160133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT294 (i+1))
      = (∑ i ∈ Finset.range 343, stT294 (i+1)) + stT294 344 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 343
    simpa using h
  have hprev := st294_p343
  have hstep := st294_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p345 : ((2070856027771/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT294 (i+1))
      = (∑ i ∈ Finset.range 344, stT294 (i+1)) + stT294 345 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 344
    simpa using h
  have hprev := st294_p344
  have hstep := st294_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p346 : ((1942239109207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT294 (i+1))
      = (∑ i ∈ Finset.range 345, stT294 (i+1)) + stT294 346 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 345
    simpa using h
  have hprev := st294_p345
  have hstep := st294_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p347 : ((1886580678487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT294 (i+1))
      = (∑ i ∈ Finset.range 346, stT294 (i+1)) + stT294 347 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 346
    simpa using h
  have hprev := st294_p346
  have hstep := st294_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p348 : ((388206300957/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT294 (i+1))
      = (∑ i ∈ Finset.range 347, stT294 (i+1)) + stT294 348 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 347
    simpa using h
  have hprev := st294_p347
  have hstep := st294_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p349 : ((4137032519271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT294 (i+1))
      = (∑ i ∈ Finset.range 348, stT294 (i+1)) + stT294 349 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 348
    simpa using h
  have hprev := st294_p348
  have hstep := st294_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p350 : ((4367255420847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT294 (i+1))
      = (∑ i ∈ Finset.range 349, stT294 (i+1)) + stT294 350 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 349
    simpa using h
  have hprev := st294_p349
  have hstep := st294_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p351 : ((4420102464687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT294 (i+1))
      = (∑ i ∈ Finset.range 350, stT294 (i+1)) + stT294 351 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 350
    simpa using h
  have hprev := st294_p350
  have hstep := st294_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p352 : ((426157247933/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT294 (i+1))
      = (∑ i ∈ Finset.range 351, stT294 (i+1)) + stT294 352 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 351
    simpa using h
  have hprev := st294_p351
  have hstep := st294_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p353 : ((3996746065269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT294 (i+1))
      = (∑ i ∈ Finset.range 352, stT294 (i+1)) + stT294 353 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 352
    simpa using h
  have hprev := st294_p352
  have hstep := st294_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p354 : ((949757614191/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT294 (i+1))
      = (∑ i ∈ Finset.range 353, stT294 (i+1)) + stT294 354 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 353
    simpa using h
  have hprev := st294_p353
  have hstep := st294_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p355 : ((1898232417717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT294 (i+1))
      = (∑ i ∈ Finset.range 354, stT294 (i+1)) + stT294 355 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 354
    simpa using h
  have hprev := st294_p354
  have hstep := st294_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p356 : ((124679068629/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT294 (i+1))
      = (∑ i ∈ Finset.range 355, stT294 (i+1)) + stT294 356 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 355
    simpa using h
  have hprev := st294_p355
  have hstep := st294_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p357 : ((1063414696081/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT294 (i+1))
      = (∑ i ∈ Finset.range 356, stT294 (i+1)) + stT294 357 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 356
    simpa using h
  have hprev := st294_p356
  have hstep := st294_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p358 : ((2209598829503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT294 (i+1))
      = (∑ i ∈ Finset.range 357, stT294 (i+1)) + stT294 358 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 357
    simpa using h
  have hprev := st294_p357
  have hstep := st294_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p359 : ((2190782944723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT294 (i+1))
      = (∑ i ∈ Finset.range 358, stT294 (i+1)) + stT294 359 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 358
    simpa using h
  have hprev := st294_p358
  have hstep := st294_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p360 : ((208277045959/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT294 (i+1))
      = (∑ i ∈ Finset.range 359, stT294 (i+1)) + stT294 360 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 359
    simpa using h
  have hprev := st294_p359
  have hstep := st294_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p361 : ((1953947908061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT294 (i+1))
      = (∑ i ∈ Finset.range 360, stT294 (i+1)) + stT294 361 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 360
    simpa using h
  have hprev := st294_p360
  have hstep := st294_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p362 : ((942517653163/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT294 (i+1))
      = (∑ i ∈ Finset.range 361, stT294 (i+1)) + stT294 362 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 361
    simpa using h
  have hprev := st294_p361
  have hstep := st294_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p363 : ((1534909313551/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT294 (i+1))
      = (∑ i ∈ Finset.range 362, stT294 (i+1)) + stT294 363 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 362
    simpa using h
  have hprev := st294_p362
  have hstep := st294_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p364 : ((8133732173837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT294 (i+1))
      = (∑ i ∈ Finset.range 363, stT294 (i+1)) + stT294 364 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 363
    simpa using h
  have hprev := st294_p363
  have hstep := st294_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p365 : ((863315675271/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT294 (i+1))
      = (∑ i ∈ Finset.range 364, stT294 (i+1)) + stT294 365 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 364
    simpa using h
  have hprev := st294_p364
  have hstep := st294_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p366 : ((886645178727/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT294 (i+1))
      = (∑ i ∈ Finset.range 365, stT294 (i+1)) + stT294 366 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 365
    simpa using h
  have hprev := st294_p365
  have hstep := st294_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p367 : ((4346303380713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT294 (i+1))
      = (∑ i ∈ Finset.range 366, stT294 (i+1)) + stT294 367 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 366
    simpa using h
  have hprev := st294_p366
  have hstep := st294_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p368 : ((4109510846111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT294 (i+1))
      = (∑ i ∈ Finset.range 367, stT294 (i+1)) + stT294 368 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 367
    simpa using h
  have hprev := st294_p367
  have hstep := st294_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p369 : ((3866477031951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT294 (i+1))
      = (∑ i ∈ Finset.range 368, stT294 (i+1)) + stT294 369 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 368
    simpa using h
  have hprev := st294_p368
  have hstep := st294_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p370 : ((3763156615773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT294 (i+1))
      = (∑ i ∈ Finset.range 369, stT294 (i+1)) + stT294 370 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 369
    simpa using h
  have hprev := st294_p369
  have hstep := st294_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p371 : ((772116754053/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT294 (i+1))
      = (∑ i ∈ Finset.range 370, stT294 (i+1)) + stT294 371 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 370
    simpa using h
  have hprev := st294_p370
  have hstep := st294_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p372 : ((1639950733281/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT294 (i+1))
      = (∑ i ∈ Finset.range 371, stT294 (i+1)) + stT294 372 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 371
    simpa using h
  have hprev := st294_p371
  have hstep := st294_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p373 : ((1735533749729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT294 (i+1))
      = (∑ i ∈ Finset.range 372, stT294 (i+1)) + stT294 373 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 372
    simpa using h
  have hprev := st294_p372
  have hstep := st294_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p374 : ((8873709874607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT294 (i+1))
      = (∑ i ∈ Finset.range 373, stT294 (i+1)) + stT294 374 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 373
    simpa using h
  have hprev := st294_p373
  have hstep := st294_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p375 : ((8674415878069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT294 (i+1))
      = (∑ i ∈ Finset.range 374, stT294 (i+1)) + stT294 375 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 374
    simpa using h
  have hprev := st294_p374
  have hstep := st294_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p376 : ((512357497647/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT294 (i+1))
      = (∑ i ∈ Finset.range 375, stT294 (i+1)) + stT294 376 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 375
    simpa using h
  have hprev := st294_p375
  have hstep := st294_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p377 : ((1930286219543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT294 (i+1))
      = (∑ i ∈ Finset.range 376, stT294 (i+1)) + stT294 377 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 376
    simpa using h
  have hprev := st294_p376
  have hstep := st294_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p378 : ((3759721214521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT294 (i+1))
      = (∑ i ∈ Finset.range 377, stT294 (i+1)) + stT294 378 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 377
    simpa using h
  have hprev := st294_p377
  have hstep := st294_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p379 : ((1926753341943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT294 (i+1))
      = (∑ i ∈ Finset.range 378, stT294 (i+1)) + stT294 379 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 378
    simpa using h
  have hprev := st294_p378
  have hstep := st294_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p380 : ((8174907043749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT294 (i+1))
      = (∑ i ∈ Finset.range 379, stT294 (i+1)) + stT294 380 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 379
    simpa using h
  have hprev := st294_p379
  have hstep := st294_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p381 : ((8656028208029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT294 (i+1))
      = (∑ i ∈ Finset.range 380, stT294 (i+1)) + stT294 381 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 380
    simpa using h
  have hprev := st294_p380
  have hstep := st294_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p382 : ((1775674054249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT294 (i+1))
      = (∑ i ∈ Finset.range 381, stT294 (i+1)) + stT294 382 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 381
    simpa using h
  have hprev := st294_p381
  have hstep := st294_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p383 : ((348723889017/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT294 (i+1))
      = (∑ i ∈ Finset.range 382, stT294 (i+1)) + stT294 383 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 382
    simpa using h
  have hprev := st294_p382
  have hstep := st294_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p384 : ((1033329985343/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT294 (i+1))
      = (∑ i ∈ Finset.range 383, stT294 (i+1)) + stT294 384 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 383
    simpa using h
  have hprev := st294_p383
  have hstep := st294_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p385 : ((194417652167/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT294 (i+1))
      = (∑ i ∈ Finset.range 384, stT294 (i+1)) + stT294 385 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 384
    simpa using h
  have hprev := st294_p384
  have hstep := st294_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p386 : ((234996739933/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT294 (i+1))
      = (∑ i ∈ Finset.range 385, stT294 (i+1)) + stT294 386 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 385
    simpa using h
  have hprev := st294_p385
  have hstep := st294_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p387 : ((954585186777/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT294 (i+1))
      = (∑ i ∈ Finset.range 386, stT294 (i+1)) + stT294 387 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 386
    simpa using h
  have hprev := st294_p386
  have hstep := st294_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p388 : ((8061237762983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT294 (i+1))
      = (∑ i ∈ Finset.range 387, stT294 (i+1)) + stT294 388 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 387
    simpa using h
  have hprev := st294_p387
  have hstep := st294_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p389 : ((8560320871903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT294 (i+1))
      = (∑ i ∈ Finset.range 388, stT294 (i+1)) + stT294 389 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 388
    simpa using h
  have hprev := st294_p388
  have hstep := st294_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p390 : ((4431209042729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT294 (i+1))
      = (∑ i ∈ Finset.range 389, stT294 (i+1)) + stT294 390 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 389
    simpa using h
  have hprev := st294_p389
  have hstep := st294_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p391 : ((2201272992037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT294 (i+1))
      = (∑ i ∈ Finset.range 390, stT294 (i+1)) + stT294 391 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 390
    simpa using h
  have hprev := st294_p390
  have hstep := st294_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p392 : ((8420805647929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT294 (i+1))
      = (∑ i ∈ Finset.range 391, stT294 (i+1)) + stT294 392 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 391
    simpa using h
  have hprev := st294_p391
  have hstep := st294_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p393 : ((7916781248337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT294 (i+1))
      = (∑ i ∈ Finset.range 392, stT294 (i+1)) + stT294 393 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 392
    simpa using h
  have hprev := st294_p392
  have hstep := st294_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p394 : ((3781044656619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT294 (i+1))
      = (∑ i ∈ Finset.range 393, stT294 (i+1)) + stT294 394 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 393
    simpa using h
  have hprev := st294_p393
  have hstep := st294_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p395 : ((3772039188429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT294 (i+1))
      = (∑ i ∈ Finset.range 394, stT294 (i+1)) + stT294 395 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 394
    simpa using h
  have hprev := st294_p394
  have hstep := st294_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p396 : ((3935350000659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT294 (i+1))
      = (∑ i ∈ Finset.range 395, stT294 (i+1)) + stT294 396 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 395
    simpa using h
  have hprev := st294_p395
  have hstep := st294_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p397 : ((8368825380783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT294 (i+1))
      = (∑ i ∈ Finset.range 396, stT294 (i+1)) + stT294 397 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 396
    simpa using h
  have hprev := st294_p396
  have hstep := st294_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p398 : ((1755463763861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT294 (i+1))
      = (∑ i ∈ Finset.range 397, stT294 (i+1)) + stT294 398 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 397
    simpa using h
  have hprev := st294_p397
  have hstep := st294_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p399 : ((8884095336341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT294 (i+1))
      = (∑ i ∈ Finset.range 398, stT294 (i+1)) + stT294 399 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 398
    simpa using h
  have hprev := st294_p398
  have hstep := st294_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p400 : ((1727045367721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT294 (i+1))
      = (∑ i ∈ Finset.range 399, stT294 (i+1)) + stT294 400 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 399
    simpa using h
  have hprev := st294_p399
  have hstep := st294_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p401 : ((510031286591/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT294 (i+1))
      = (∑ i ∈ Finset.range 400, stT294 (i+1)) + stT294 401 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 400
    simpa using h
  have hprev := st294_p400
  have hstep := st294_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p402 : ((7704313825951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT294 (i+1))
      = (∑ i ∈ Finset.range 401, stT294 (i+1)) + stT294 402 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 401
    simpa using h
  have hprev := st294_p401
  have hstep := st294_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p403 : ((7499347300439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT294 (i+1))
      = (∑ i ∈ Finset.range 402, stT294 (i+1)) + stT294 403 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 402
    simpa using h
  have hprev := st294_p402
  have hstep := st294_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p404 : ((7648540510689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT294 (i+1))
      = (∑ i ∈ Finset.range 403, stT294 (i+1)) + stT294 404 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 403
    simpa using h
  have hprev := st294_p403
  have hstep := st294_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p405 : ((807486688689/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT294 (i+1))
      = (∑ i ∈ Finset.range 404, stT294 (i+1)) + stT294 405 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 404
    simpa using h
  have hprev := st294_p404
  have hstep := st294_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p406 : ((2140643261293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT294 (i+1))
      = (∑ i ∈ Finset.range 405, stT294 (i+1)) + stT294 406 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 405
    simpa using h
  have hprev := st294_p405
  have hstep := st294_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p407 : ((886714820107/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT294 (i+1))
      = (∑ i ∈ Finset.range 406, stT294 (i+1)) + stT294 407 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 406
    simpa using h
  have hprev := st294_p406
  have hstep := st294_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p408 : ((220939621429/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT294 (i+1))
      = (∑ i ∈ Finset.range 407, stT294 (i+1)) + stT294 408 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 407
    simpa using h
  have hprev := st294_p407
  have hstep := st294_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p409 : ((4245004870433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT294 (i+1))
      = (∑ i ∈ Finset.range 408, stT294 (i+1)) + stT294 409 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 408
    simpa using h
  have hprev := st294_p408
  have hstep := st294_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p410 : ((7997428296001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT294 (i+1))
      = (∑ i ∈ Finset.range 409, stT294 (i+1)) + stT294 410 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 409
    simpa using h
  have hprev := st294_p409
  have hstep := st294_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p411 : ((1520507779021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT294 (i+1))
      = (∑ i ∈ Finset.range 410, stT294 (i+1)) + stT294 411 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 410
    simpa using h
  have hprev := st294_p410
  have hstep := st294_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p412 : ((1499609126787/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT294 (i+1))
      = (∑ i ∈ Finset.range 411, stT294 (i+1)) + stT294 412 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 411
    simpa using h
  have hprev := st294_p411
  have hstep := st294_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p413 : ((7733515439579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT294 (i+1))
      = (∑ i ∈ Finset.range 412, stT294 (i+1)) + stT294 413 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 412
    simpa using h
  have hprev := st294_p412
  have hstep := st294_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p414 : ((2048328619787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT294 (i+1))
      = (∑ i ∈ Finset.range 413, stT294 (i+1)) + stT294 414 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 413
    simpa using h
  have hprev := st294_p413
  have hstep := st294_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p415 : ((2163654371627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT294 (i+1))
      = (∑ i ∈ Finset.range 414, stT294 (i+1)) + stT294 415 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 414
    simpa using h
  have hprev := st294_p414
  have hstep := st294_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p416 : ((555993013433/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT294 (i+1))
      = (∑ i ∈ Finset.range 415, stT294 (i+1)) + stT294 416 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 415
    simpa using h
  have hprev := st294_p415
  have hstep := st294_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p417 : ((220068471727/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT294 (i+1))
      = (∑ i ∈ Finset.range 416, stT294 (i+1)) + stT294 417 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 416
    simpa using h
  have hprev := st294_p416
  have hstep := st294_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p418 : ((2105233363033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT294 (i+1))
      = (∑ i ∈ Finset.range 417, stT294 (i+1)) + stT294 418 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 417
    simpa using h
  have hprev := st294_p417
  have hstep := st294_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p419 : ((1983133338943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT294 (i+1))
      = (∑ i ∈ Finset.range 418, stT294 (i+1)) + stT294 419 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 418
    simpa using h
  have hprev := st294_p418
  have hstep := st294_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p420 : ((7568233530731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT294 (i+1))
      = (∑ i ∈ Finset.range 419, stT294 (i+1)) + stT294 420 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 419
    simpa using h
  have hprev := st294_p419
  have hstep := st294_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p421 : ((3749216371741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT294 (i+1))
      = (∑ i ∈ Finset.range 420, stT294 (i+1)) + stT294 421 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 420
    simpa using h
  have hprev := st294_p420
  have hstep := st294_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p422 : ((3877221005497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT294 (i+1))
      = (∑ i ∈ Finset.range 421, stT294 (i+1)) + stT294 422 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 421
    simpa using h
  have hprev := st294_p421
  have hstep := st294_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p423 : ((4107882605221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT294 (i+1))
      = (∑ i ∈ Finset.range 422, stT294 (i+1)) + stT294 423 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 422
    simpa using h
  have hprev := st294_p422
  have hstep := st294_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p424 : ((2166983826719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT294 (i+1))
      = (∑ i ∈ Finset.range 423, stT294 (i+1)) + stT294 424 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 423
    simpa using h
  have hprev := st294_p423
  have hstep := st294_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p425 : ((8902589858339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT294 (i+1))
      = (∑ i ∈ Finset.range 424, stT294 (i+1)) + stT294 425 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 424
    simpa using h
  have hprev := st294_p424
  have hstep := st294_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p426 : ((1762597502393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT294 (i+1))
      = (∑ i ∈ Finset.range 425, stT294 (i+1)) + stT294 426 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 425
    simpa using h
  have hprev := st294_p425
  have hstep := st294_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p427 : ((8441421534963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT294 (i+1))
      = (∑ i ∈ Finset.range 426, stT294 (i+1)) + stT294 427 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 426
    simpa using h
  have hprev := st294_p426
  have hstep := st294_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p428 : ((3979009591251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT294 (i+1))
      = (∑ i ∈ Finset.range 427, stT294 (i+1)) + stT294 428 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 427
    simpa using h
  have hprev := st294_p427
  have hstep := st294_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p429 : ((473877174297/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT294 (i+1))
      = (∑ i ∈ Finset.range 428, stT294 (i+1)) + stT294 429 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 428
    simpa using h
  have hprev := st294_p428
  have hstep := st294_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p430 : ((7482405796167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT294 (i+1))
      = (∑ i ∈ Finset.range 429, stT294 (i+1)) + stT294 430 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 429
    simpa using h
  have hprev := st294_p429
  have hstep := st294_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p431 : ((7702611996447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT294 (i+1))
      = (∑ i ∈ Finset.range 430, stT294 (i+1)) + stT294 431 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 430
    simpa using h
  have hprev := st294_p430
  have hstep := st294_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p432 : ((8142938558697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT294 (i+1))
      = (∑ i ∈ Finset.range 431, stT294 (i+1)) + stT294 432 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 431
    simpa using h
  have hprev := st294_p431
  have hstep := st294_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p433 : ((8606653042729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT294 (i+1))
      = (∑ i ∈ Finset.range 432, stT294 (i+1)) + stT294 433 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 432
    simpa using h
  have hprev := st294_p432
  have hstep := st294_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p434 : ((2222093581561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT294 (i+1))
      = (∑ i ∈ Finset.range 433, stT294 (i+1)) + stT294 434 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 433
    simpa using h
  have hprev := st294_p433
  have hstep := st294_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p435 : ((88647027091/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT294 (i+1))
      = (∑ i ∈ Finset.range 434, stT294 (i+1)) + stT294 435 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 434
    simpa using h
  have hprev := st294_p434
  have hstep := st294_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p436 : ((4273647157031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT294 (i+1))
      = (∑ i ∈ Finset.range 435, stT294 (i+1)) + stT294 436 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 435
    simpa using h
  have hprev := st294_p435
  have hstep := st294_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p437 : ((126187717183/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT294 (i+1))
      = (∑ i ∈ Finset.range 436, stT294 (i+1)) + stT294 437 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 436
    simpa using h
  have hprev := st294_p436
  have hstep := st294_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p438 : ((7656440557993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT294 (i+1))
      = (∑ i ∈ Finset.range 437, stT294 (i+1)) + stT294 438 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 437
    simpa using h
  have hprev := st294_p437
  have hstep := st294_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p439 : ((7470005401743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT294 (i+1))
      = (∑ i ∈ Finset.range 438, stT294 (i+1)) + stT294 439 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 438
    simpa using h
  have hprev := st294_p438
  have hstep := st294_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p440 : ((3798038218981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT294 (i+1))
      = (∑ i ∈ Finset.range 439, stT294 (i+1)) + stT294 440 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 439
    simpa using h
  have hprev := st294_p439
  have hstep := st294_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p441 : ((997401471139/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT294 (i+1))
      = (∑ i ∈ Finset.range 440, stT294 (i+1)) + stT294 441 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 440
    simpa using h
  have hprev := st294_p440
  have hstep := st294_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p442 : ((4227298677927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT294 (i+1))
      = (∑ i ∈ Finset.range 441, stT294 (i+1)) + stT294 442 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 441
    simpa using h
  have hprev := st294_p441
  have hstep := st294_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p443 : ((275611353177/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT294 (i+1))
      = (∑ i ∈ Finset.range 442, stT294 (i+1)) + stT294 443 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 442
    simpa using h
  have hprev := st294_p442
  have hstep := st294_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p444 : ((4459968986199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT294 (i+1))
      = (∑ i ∈ Finset.range 443, stT294 (i+1)) + stT294 444 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 443
    simpa using h
  have hprev := st294_p443
  have hstep := st294_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p445 : ((544654187507/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT294 (i+1))
      = (∑ i ∈ Finset.range 444, stT294 (i+1)) + stT294 445 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 444
    simpa using h
  have hprev := st294_p444
  have hstep := st294_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p446 : ((4145343324523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT294 (i+1))
      = (∑ i ∈ Finset.range 445, stT294 (i+1)) + stT294 446 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 445
    simpa using h
  have hprev := st294_p445
  have hstep := st294_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p447 : ((3913345854983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT294 (i+1))
      = (∑ i ∈ Finset.range 446, stT294 (i+1)) + stT294 447 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 446
    simpa using h
  have hprev := st294_p446
  have hstep := st294_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p448 : ((3757910901947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT294 (i+1))
      = (∑ i ∈ Finset.range 447, stT294 (i+1)) + stT294 448 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 447
    simpa using h
  have hprev := st294_p447
  have hstep := st294_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p449 : ((233946704987/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT294 (i+1))
      = (∑ i ∈ Finset.range 448, stT294 (i+1)) + stT294 449 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 448
    simpa using h
  have hprev := st294_p448
  have hstep := st294_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p450 : ((242160212581/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT294 (i+1))
      = (∑ i ∈ Finset.range 449, stT294 (i+1)) + stT294 450 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 449
    simpa using h
  have hprev := st294_p449
  have hstep := st294_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p451 : ((1024383272223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT294 (i+1))
      = (∑ i ∈ Finset.range 450, stT294 (i+1)) + stT294 451 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 450
    simpa using h
  have hprev := st294_p450
  have hstep := st294_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p452 : ((540051676259/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT294 (i+1))
      = (∑ i ∈ Finset.range 451, stT294 (i+1)) + stT294 452 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 451
    simpa using h
  have hprev := st294_p451
  have hstep := st294_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p453 : ((556545174539/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT294 (i+1))
      = (∑ i ∈ Finset.range 452, stT294 (i+1)) + stT294 453 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 452
    simpa using h
  have hprev := st294_p452
  have hstep := st294_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p454 : ((444020097681/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT294 (i+1))
      = (∑ i ∈ Finset.range 453, stT294 (i+1)) + stT294 454 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 453
    simpa using h
  have hprev := st294_p453
  have hstep := st294_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p455 : ((2144707840663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT294 (i+1))
      = (∑ i ∈ Finset.range 454, stT294 (i+1)) + stT294 455 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 454
    simpa using h
  have hprev := st294_p454
  have hstep := st294_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p456 : ((4061237575611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT294 (i+1))
      = (∑ i ∈ Finset.range 455, stT294 (i+1)) + stT294 456 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 455
    simpa using h
  have hprev := st294_p455
  have hstep := st294_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p457 : ((7694787192951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT294 (i+1))
      = (∑ i ∈ Finset.range 456, stT294 (i+1)) + stT294 457 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 456
    simpa using h
  have hprev := st294_p456
  have hstep := st294_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p458 : ((7466270668531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT294 (i+1))
      = (∑ i ∈ Finset.range 457, stT294 (i+1)) + stT294 458 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 457
    simpa using h
  have hprev := st294_p457
  have hstep := st294_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p459 : ((7526899991971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT294 (i+1))
      = (∑ i ∈ Finset.range 458, stT294 (i+1)) + stT294 459 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 458
    simpa using h
  have hprev := st294_p458
  have hstep := st294_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p460 : ((7851483186779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT294 (i+1))
      = (∑ i ∈ Finset.range 459, stT294 (i+1)) + stT294 460 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 459
    simpa using h
  have hprev := st294_p459
  have hstep := st294_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p461 : ((8311071093167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT294 (i+1))
      = (∑ i ∈ Finset.range 460, stT294 (i+1)) + stT294 461 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 460
    simpa using h
  have hprev := st294_p460
  have hstep := st294_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p462 : ((8724790798361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT294 (i+1))
      = (∑ i ∈ Finset.range 461, stT294 (i+1)) + stT294 462 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 461
    simpa using h
  have hprev := st294_p461
  have hstep := st294_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p463 : ((2232792210077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT294 (i+1))
      = (∑ i ∈ Finset.range 462, stT294 (i+1)) + stT294 463 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 462
    simpa using h
  have hprev := st294_p462
  have hstep := st294_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p464 : ((1770145379821/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT294 (i+1))
      = (∑ i ∈ Finset.range 463, stT294 (i+1)) + stT294 464 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 463
    simpa using h
  have hprev := st294_p463
  have hstep := st294_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p465 : ((68126071557/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT294 (i+1))
      = (∑ i ∈ Finset.range 464, stT294 (i+1)) + stT294 465 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 464
    simpa using h
  have hprev := st294_p464
  have hstep := st294_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p466 : ((8056513796601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT294 (i+1))
      = (∑ i ∈ Finset.range 465, stT294 (i+1)) + stT294 466 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 465
    simpa using h
  have hprev := st294_p465
  have hstep := st294_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p467 : ((7649927529801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT294 (i+1))
      = (∑ i ∈ Finset.range 466, stT294 (i+1)) + stT294 467 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 466
    simpa using h
  have hprev := st294_p466
  have hstep := st294_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p468 : ((7451348198209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT294 (i+1))
      = (∑ i ∈ Finset.range 467, stT294 (i+1)) + stT294 468 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 467
    simpa using h
  have hprev := st294_p467
  have hstep := st294_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p469 : ((7535610539083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT294 (i+1))
      = (∑ i ∈ Finset.range 468, stT294 (i+1)) + stT294 469 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 468
    simpa using h
  have hprev := st294_p468
  have hstep := st294_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p470 : ((3934794961799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT294 (i+1))
      = (∑ i ∈ Finset.range 469, stT294 (i+1)) + stT294 470 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 469
    simpa using h
  have hprev := st294_p469
  have hstep := st294_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p471 : ((8326056216573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT294 (i+1))
      = (∑ i ∈ Finset.range 470, stT294 (i+1)) + stT294 471 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 470
    simpa using h
  have hprev := st294_p470
  have hstep := st294_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p472 : ((1091586808161/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT294 (i+1))
      = (∑ i ∈ Finset.range 471, stT294 (i+1)) + stT294 472 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 471
    simpa using h
  have hprev := st294_p471
  have hstep := st294_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p473 : ((1117156516061/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT294 (i+1))
      = (∑ i ∈ Finset.range 472, stT294 (i+1)) + stT294 473 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 472
    simpa using h
  have hprev := st294_p472
  have hstep := st294_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p474 : ((17728264473/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT294 (i+1))
      = (∑ i ∈ Finset.range 473, stT294 (i+1)) + stT294 474 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 473
    simpa using h
  have hprev := st294_p473
  have hstep := st294_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p475 : ((2135400561729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT294 (i+1))
      = (∑ i ∈ Finset.range 474, stT294 (i+1)) + stT294 475 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 474
    simpa using h
  have hprev := st294_p474
  have hstep := st294_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p476 : ((4045029601383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT294 (i+1))
      = (∑ i ∈ Finset.range 475, stT294 (i+1)) + stT294 476 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 475
    simpa using h
  have hprev := st294_p475
  have hstep := st294_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p477 : ((7676509632621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT294 (i+1))
      = (∑ i ∈ Finset.range 476, stT294 (i+1)) + stT294 477 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 476
    simpa using h
  have hprev := st294_p476
  have hstep := st294_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p478 : ((7452689495241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT294 (i+1))
      = (∑ i ∈ Finset.range 477, stT294 (i+1)) + stT294 478 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 477
    simpa using h
  have hprev := st294_p477
  have hstep := st294_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p479 : ((937463033301/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT294 (i+1))
      = (∑ i ∈ Finset.range 478, stT294 (i+1)) + stT294 479 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 478
    simpa using h
  have hprev := st294_p478
  have hstep := st294_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p480 : ((3899684681349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT294 (i+1))
      = (∑ i ∈ Finset.range 479, stT294 (i+1)) + stT294 480 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 479
    simpa using h
  have hprev := st294_p479
  have hstep := st294_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p481 : ((4120965489049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT294 (i+1))
      = (∑ i ∈ Finset.range 480, stT294 (i+1)) + stT294 481 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 480
    simpa using h
  have hprev := st294_p480
  have hstep := st294_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p482 : ((4333438331887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT294 (i+1))
      = (∑ i ∈ Finset.range 481, stT294 (i+1)) + stT294 482 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 481
    simpa using h
  have hprev := st294_p481
  have hstep := st294_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p483 : ((8921297846009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT294 (i+1))
      = (∑ i ∈ Finset.range 482, stT294 (i+1)) + stT294 483 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 482
    simpa using h
  have hprev := st294_p482
  have hstep := st294_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p484 : ((8914615565263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT294 (i+1))
      = (∑ i ∈ Finset.range 483, stT294 (i+1)) + stT294 484 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 483
    simpa using h
  have hprev := st294_p483
  have hstep := st294_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p485 : ((1730044574987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT294 (i+1))
      = (∑ i ∈ Finset.range 484, stT294 (i+1)) + stT294 485 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 484
    simpa using h
  have hprev := st294_p484
  have hstep := st294_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p486 : ((65784934829/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT294 (i+1))
      = (∑ i ∈ Finset.range 485, stT294 (i+1)) + stT294 486 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 485
    simpa using h
  have hprev := st294_p485
  have hstep := st294_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p487 : ((7785214805209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT294 (i+1))
      = (∑ i ∈ Finset.range 486, stT294 (i+1)) + stT294 487 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 486
    simpa using h
  have hprev := st294_p486
  have hstep := st294_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p488 : ((1498210444271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT294 (i+1))
      = (∑ i ∈ Finset.range 487, stT294 (i+1)) + stT294 488 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 487
    simpa using h
  have hprev := st294_p487
  have hstep := st294_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p489 : ((7443428902179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT294 (i+1))
      = (∑ i ∈ Finset.range 488, stT294 (i+1)) + stT294 489 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 488
    simpa using h
  have hprev := st294_p488
  have hstep := st294_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p490 : ((1914515656317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT294 (i+1))
      = (∑ i ∈ Finset.range 489, stT294 (i+1)) + stT294 490 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 489
    simpa using h
  have hprev := st294_p489
  have hstep := st294_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p491 : ((8059104601011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT294 (i+1))
      = (∑ i ∈ Finset.range 490, stT294 (i+1)) + stT294 491 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 490
    simpa using h
  have hprev := st294_p490
  have hstep := st294_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p492 : ((8506542919323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT294 (i+1))
      = (∑ i ∈ Finset.range 491, stT294 (i+1)) + stT294 492 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 491
    simpa using h
  have hprev := st294_p491
  have hstep := st294_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p493 : ((276419138407/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT294 (i+1))
      = (∑ i ∈ Finset.range 492, stT294 (i+1)) + stT294 493 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 492
    simpa using h
  have hprev := st294_p492
  have hstep := st294_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p494 : ((8959340074881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT294 (i+1))
      = (∑ i ∈ Finset.range 493, stT294 (i+1)) + stT294 494 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 493
    simpa using h
  have hprev := st294_p493
  have hstep := st294_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p495 : ((8810073882049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT294 (i+1))
      = (∑ i ∈ Finset.range 494, stT294 (i+1)) + stT294 495 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 494
    simpa using h
  have hprev := st294_p494
  have hstep := st294_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p496 : ((8449615770171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT294 (i+1))
      = (∑ i ∈ Finset.range 495, stT294 (i+1)) + stT294 496 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 495
    simpa using h
  have hprev := st294_p495
  have hstep := st294_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p497 : ((8001501883609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT294 (i+1))
      = (∑ i ∈ Finset.range 496, stT294 (i+1)) + stT294 497 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 496
    simpa using h
  have hprev := st294_p496
  have hstep := st294_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p498 : ((1904511644811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT294 (i+1))
      = (∑ i ∈ Finset.range 497, stT294 (i+1)) + stT294 498 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 497
    simpa using h
  have hprev := st294_p497
  have hstep := st294_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p499 : ((3714275851153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT294 (i+1))
      = (∑ i ∈ Finset.range 498, stT294 (i+1)) + stT294 499 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 498
    simpa using h
  have hprev := st294_p498
  have hstep := st294_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_p500 : ((7496051796461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT294 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT294 (i+1))
      = (∑ i ∈ Finset.range 499, stT294 (i+1)) + stT294 500 := by
    have h := Finset.sum_range_succ (fun i => stT294 (i+1)) 499
    simpa using h
  have hprev := st294_p499
  have hstep := st294_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st294_s500 :
    |Real.sin (((294 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((6689/62500 : ℚ) : ℝ))
      - ((-61783/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1773977/5000000) (δ := 14791/1000000000) (ψ := 6689/62500) 294 291
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 294`** (evaluated boundary). -/
theorem station_294_sign : hardyG ((((294:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 294 500 (by norm_num) (by norm_num)
    ((6689/62500 : ℚ) : ℝ)
  have hchain := st294_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT294 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((294 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((6689/62500 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st294_c500
  have hsinb := abs_le.mp st294_s500
  have hbdy_lo : ((259850666947677/3457450000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((294 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((6689/62500 : ℚ) : ℝ))) / 2
          - ((((294:ℕ)):ℝ))
            * Real.sin (((294 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((6689/62500 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((294:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((294:ℝ) * Real.log (500:ℝ) - ((6689/62500 : ℚ) : ℝ))) / 2
        - ((294:ℝ)) * Real.sin ((294:ℝ) * Real.log (500:ℝ) - ((6689/62500 : ℚ) : ℝ))
        ≥ ((581044529/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((294:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((581044529/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((581044529/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((581044529/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((294:ℕ)):ℝ))+1) * (((((294:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((506369008243/750000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((7496051796461/10000000000000 : ℚ) : ℝ) + ((259850666947677/3457450000000000 : ℚ) : ℝ)
      - ((506369008243/750000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((6689/62500 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((294:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((6689/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((294:ℕ)):ℝ)))).re
      - Real.sin ((6689/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((294:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((294:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((294:ℕ)):ℝ))
      = (((((294:ℕ)):ℝ)) * (Real.log ((((294:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((294:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_294
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
  have hθwin : |(((6689/62500 : ℚ) : ℝ) + ((67:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((294:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((294:ℕ)):ℝ)))
    (φ := ((6689/62500 : ℚ) : ℝ) + ((67:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((6689/62500 : ℚ) : ℝ) + ((67:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((6689/62500 : ℚ)) : ℝ) - Real.pi) + ((67:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((6689/62500 : ℚ)) : ℝ) - Real.pi) 67).1,
    (cos_sin_shift ((((6689/62500 : ℚ)) : ℝ) - Real.pi) 67).2]
  exact cos_sin_flip ((6689/62500 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_294_sign
end AxiomAudit
