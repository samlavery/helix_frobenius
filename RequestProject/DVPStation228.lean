import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 228` (rung-235.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT228 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((228 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))

theorem st228_c1 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((48297/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327179/5000000) (δ := 201/1000000000) (ψ := -261743/1000000) 228 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t1 : ((96589/100000 : ℚ) : ℝ) ≤ stT228 1 := by
  have hc : ((96589/100000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96589/100000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((96589/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c2 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((68793/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3049151/10000000) (δ := 5761/500000000) (ψ := -261743/1000000) 228 25
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t2 : ((486369201461/2000000000000 : ℚ) : ℝ) ≤ stT228 2 := by
  have hc : ((68783/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486369201461/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((68783/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c3 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((835323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1455191/10000000) (δ := 5757/500000000) (ψ := -261743/1000000) 228 40
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t3 : ((2411225168023/5000000000000 : ℚ) : ℝ) ≤ stT228 3 := by
  have hc : ((835273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2411225168023/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((835273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c4 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-142559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2721987/5000000) (δ := 289/25000000) (ψ := -261743/1000000) 228 50
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t4 : ((-1425715285143/5000000000000 : ℚ) : ℝ) ≤ stT228 4 := by
  have hc : ((-285143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1425715285143/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-285143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c5 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-234607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6972119/10000000) (δ := 2317/200000000) (ψ := -261743/1000000) 228 58
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t5 : ((-262312578063/625000000000 : ℚ) : ℝ) ≤ stT228 5 := by
  have hc : ((-469239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262312578063/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-469239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c6 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((186039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58727/625000) (δ := 723/62500000) (ψ := -261743/1000000) 228 65
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t6 : ((379730021989/1000000000000 : ℚ) : ℝ) ≤ stT228 6 := by
  have hc : ((186029/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379730021989/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((186029/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c7 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-569669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5442249/10000000) (δ := 11411/1000000000) (ψ := -261743/1000000) 228 71
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t7 : ((-430667113951/2000000000000 : ℚ) : ℝ) ≤ stT228 7 := by
  have hc : ((-569719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-430667113951/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-569719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c8 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-499991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1959699/2500000) (δ := 143/12500000) (ψ := -261743/1000000) 228 75
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t8 : ((-55244486517/156250000000 : ℚ) : ℝ) ≤ stT228 8 := by
  have hc : ((-31251/31250 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55244486517/156250000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-31251/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c9 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((72203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -356471/1000000) (δ := 1447/125000000) (ψ := -261743/1000000) 228 80
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t9 : ((120296654637/2500000000000 : ℚ) : ℝ) ≤ stT228 9 := by
  have hc : ((36089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120296654637/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((36089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c10 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-82241/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6341079/10000000) (δ := 5799/500000000) (ψ := -261743/1000000) 228 84
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t10 : ((-65021179097/250000000000 : ℚ) : ℝ) ≤ stT228 10 := by
  have hc : ((-41123/50000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65021179097/250000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-41123/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c11 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((235291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 430923/5000000) (δ := 5763/500000000) (ψ := -261743/1000000) 228 87
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t11 : ((1418782527941/5000000000000 : ℚ) : ℝ) ≤ stT228 11 := by
  have hc : ((470557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1418782527941/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((470557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c12 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((117401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1667227/5000000) (δ := 1431/125000000) (ψ := -261743/1000000) 228 90
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t12 : ((2647150667/39062500000 : ℚ) : ℝ) ≤ stT228 12 := by
  have hc : ((3668/15625 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2647150667/39062500000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((3668/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c13 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((742527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1834903/10000000) (δ := 5717/500000000) (ψ := -261743/1000000) 228 93
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t13 : ((4118519919/20000000000 : ℚ) : ℝ) ≤ stT228 13 := by
  have hc : ((742477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4118519919/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((742477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c14 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((86153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3047427/10000000) (δ := 1439/125000000) (ψ := -261743/1000000) 228 96
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t14 : ((115110066993/1250000000000 : ℚ) : ℝ) ≤ stT228 14 := by
  have hc : ((172281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115110066993/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((172281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c15 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-365569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24313/50000) (δ := 2301/200000000) (ψ := -261743/1000000) 228 98
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t15 : ((-944024236191/10000000000000 : ℚ) : ℝ) ≤ stT228 15 := by
  have hc : ((-365619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-944024236191/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-365619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c16 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-580173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1094869/2000000) (δ := 11427/1000000000) (ψ := -261743/1000000) 228 101
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t16 : ((-1450558080223/10000000000000 : ℚ) : ℝ) ≤ stT228 16 := by
  have hc : ((-580223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1450558080223/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-580223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c17 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((37179/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9337/40000) (δ := 5781/500000000) (ψ := -261743/1000000) 228 103
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t17 : ((180329462973/1250000000000 : ℚ) : ℝ) ≤ stT228 17 := by
  have hc : ((297407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180329462973/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((297407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c18 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((223123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36559/312500) (δ := 2291/200000000) (ψ := -261743/1000000) 228 105
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t18 : ((525876356931/2500000000000 : ℚ) : ℝ) ≤ stT228 18 := by
  have hc : ((446221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525876356931/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((446221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c19 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((760311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1767511/10000000) (δ := 11533/1000000000) (ψ := -261743/1000000) 228 107
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t19 : ((1744158094977/10000000000000 : ℚ) : ℝ) ≤ stT228 19 := by
  have hc : ((760261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1744158094977/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((760261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c20 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-3853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246641/625000) (δ := 2871/250000000) (ψ := -261743/1000000) 228 109
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t20 : ((-1083933963/625000000000 : ℚ) : ℝ) ≤ stT228 20 := by
  have hc : ((-1939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1083933963/625000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-1939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c21 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-496351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7551769/10000000) (δ := 2301/200000000) (ψ := -261743/1000000) 228 111
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t21 : ((-135397660413/625000000000 : ℚ) : ℝ) ≤ stT228 21 := by
  have hc : ((-62047/62500 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135397660413/625000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-62047/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c22 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((8279/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 814167/2500000) (δ := 5703/500000000) (ψ := -261743/1000000) 228 112
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t22 : ((282360875073/5000000000000 : ℚ) : ℝ) ≤ stT228 22 := by
  have hc : ((132439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282360875073/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((132439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c23 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((427841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2821733/10000000) (δ := 11583/1000000000) (ψ := -261743/1000000) 228 114
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t23 : ((111500729613/1250000000000 : ℚ) : ℝ) ≤ stT228 23 := by
  have hc : ((427791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111500729613/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((427791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c24 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-82509/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1432319/2500000) (δ := 2869/250000000) (ψ := -261743/1000000) 228 115
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t24 : ((-336867187881/2500000000000 : ℚ) : ℝ) ≤ stT228 24 := by
  have hc : ((-330061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336867187881/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-330061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c25 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((567571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241811/1000000) (δ := 5771/500000000) (ψ := -261743/1000000) 228 117
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t25 : ((567521/5000000 : ℚ) : ℝ) ≤ stT228 25 := by
  have hc : ((567521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567521/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((567521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c26 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-60399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169189/400000) (δ := 5777/500000000) (ψ := -261743/1000000) 228 118
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t26 : ((-7406328293/312500000000 : ℚ) : ℝ) ≤ stT228 26 := by
  have hc : ((-7553/62500 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7406328293/312500000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-7553/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c27 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-643373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -567423/1000000) (δ := 11463/1000000000) (ψ := -261743/1000000) 228 120
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t27 : ((-1238268206923/10000000000000 : ℚ) : ℝ) ≤ stT228 27 := by
  have hc : ((-643423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1238268206923/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-643423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c28 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((483061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163151/2500000) (δ := 1157/100000000) (ψ := -261743/1000000) 228 121
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t28 : ((114106507449/625000000000 : ℚ) : ℝ) ≤ stT228 28 := by
  have hc : ((120759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114106507449/625000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((120759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c29 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((113959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3641473/10000000) (δ := 5763/500000000) (ψ := -261743/1000000) 228 122
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t29 : ((211523659277/10000000000000 : ℚ) : ℝ) ≤ stT228 29 := by
  have hc : ((113909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211523659277/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((113909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c30 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-971659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1451473/2000000) (δ := 5709/500000000) (ψ := -261743/1000000) 228 123
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t30 : ((-887044966539/5000000000000 : ℚ) : ℝ) ≤ stT228 30 := by
  have hc : ((-971709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-887044966539/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-971709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c31 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-18069/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2734159/5000000) (δ := 11599/1000000000) (ψ := -261743/1000000) 228 125
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t31 : ((-259645648483/2500000000000 : ℚ) : ℝ) ≤ stT228 31 := by
  have hc : ((-289129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259645648483/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-289129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c32 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((83133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3079523/10000000) (δ := 11497/1000000000) (ψ := -261743/1000000) 228 126
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t32 : ((146937593803/2500000000000 : ℚ) : ℝ) ≤ stT228 32 := by
  have hc : ((166241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146937593803/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((166241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c33 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((219507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -623837/5000000) (δ := 11413/1000000000) (ψ := -261743/1000000) 228 127
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t33 : ((95522689433/625000000000 : ℚ) : ℝ) ≤ stT228 33 := by
  have hc : ((438989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95522689433/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((438989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c34 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((499853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60573/10000000) (δ := 9/781250) (ψ := -261743/1000000) 228 128
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t34 : ((42859876129/250000000000 : ℚ) : ℝ) ≤ stT228 34 := by
  have hc : ((124957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42859876129/250000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((124957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c35 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((469653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 218871/2500000) (δ := 463/40000000) (ψ := -261743/1000000) 228 129
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t35 : ((49613497839/312500000000 : ℚ) : ℝ) ≤ stT228 35 := by
  have hc : ((117407/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49613497839/312500000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((117407/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c36 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((176469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 612467/5000000) (δ := 2867/250000000) (ψ := -261743/1000000) 228 130
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t36 : ((147049107847/1000000000000 : ℚ) : ℝ) ≤ stT228 36 := by
  have hc : ((176459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147049107847/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((176459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c37 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((179761/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1134401/10000000) (δ := 5721/500000000) (ψ := -261743/1000000) 228 131
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t37 : ((295508666739/2000000000000 : ℚ) : ℝ) ≤ stT228 37 := by
  have hc : ((179751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295508666739/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((179751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c38 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((968683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39207/625000) (δ := 11549/1000000000) (ψ := -261743/1000000) 228 132
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t38 : ((785665006731/5000000000000 : ℚ) : ℝ) ≤ stT228 38 := by
  have hc : ((968633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((785665006731/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((968633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c39 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((993973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274617/10000000) (δ := 11547/1000000000) (ψ := -261743/1000000) 228 133
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t39 : ((1591550015363/10000000000000 : ℚ) : ℝ) ≤ stT228 39 := by
  have hc : ((993923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1591550015363/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((993923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c40 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((162709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -775717/5000000) (δ := 11439/1000000000) (ψ := -261743/1000000) 228 134
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t40 : ((128624785731/1000000000000 : ℚ) : ℝ) ≤ stT228 40 := by
  have hc : ((162699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128624785731/1000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((162699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c41 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((58521/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636923/2000000) (δ := 11471/1000000000) (ψ := -261743/1000000) 228 135
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t41 : ((91378793607/2000000000000 : ℚ) : ℝ) ≤ stT228 41 := by
  have hc : ((58511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91378793607/2000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((58511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c42 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-236187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2578473/5000000) (δ := 5789/500000000) (ψ := -261743/1000000) 228 136
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t42 : ((-45560393401/625000000000 : ℚ) : ℝ) ≤ stT228 42 := by
  have hc : ((-59053/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45560393401/625000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-59053/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c43 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-493567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298101/400000) (δ := 5759/500000000) (ψ := -261743/1000000) 228 137
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t43 : ((-47045055607/312500000000 : ℚ) : ℝ) ≤ stT228 43 := by
  have hc : ((-61699/62500 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47045055607/312500000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-61699/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c44 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-636383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565149/1000000) (δ := 5759/500000000) (ψ := -261743/1000000) 228 137
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t44 : ((-959459024181/10000000000000 : ℚ) : ℝ) ≤ stT228 44 := by
  have hc : ((-636433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-959459024181/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-636433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c45 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((226259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2753023/10000000) (δ := 11411/1000000000) (ψ := -261743/1000000) 228 138
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t45 : ((168624756187/2500000000000 : ℚ) : ℝ) ≤ stT228 45 := by
  have hc : ((113117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168624756187/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((113117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c46 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((985451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426967/10000000) (δ := 11499/1000000000) (ψ := -261743/1000000) 228 139
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t46 : ((1452893957019/10000000000000 : ℚ) : ℝ) ≤ stT228 46 := by
  have hc : ((985401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1452893957019/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((985401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c47 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((20259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193817/500000) (δ := 2899/250000000) (ψ := -261743/1000000) 228 140
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t47 : ((29477837641/10000000000000 : ℚ) : ℝ) ≤ stT228 47 := by
  have hc : ((20209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29477837641/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((20209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c48 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-994169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1516773/2000000) (δ := 11489/1000000000) (ψ := -261743/1000000) 228 141
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t48 : ((-89689490209/625000000000 : ℚ) : ℝ) ≤ stT228 48 := by
  have hc : ((-994219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89689490209/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-994219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c49 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-24171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4169079/10000000) (δ := 11489/1000000000) (ψ := -261743/1000000) 228 141
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t49 : ((-17273935481/1250000000000 : ℚ) : ℝ) ≤ stT228 49 := by
  have hc : ((-48367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17273935481/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-48367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c50 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((999957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2911/1250000) (δ := 11421/1000000000) (ψ := -261743/1000000) 228 142
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t50 : ((1414081478191/10000000000000 : ℚ) : ℝ) ≤ stT228 50 := by
  have hc : ((999907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1414081478191/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((999907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c51 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-102621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4443769/10000000) (δ := 1441/125000000) (ψ := -261743/1000000) 228 143
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t51 : ((-71866621763/2500000000000 : ℚ) : ℝ) ≤ stT228 51 := by
  have hc : ((-51323/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71866621763/2500000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-51323/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c52 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-881497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1656137/2500000) (δ := 1441/125000000) (ψ := -261743/1000000) 228 143
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t52 : ((-1222486183797/10000000000000 : ℚ) : ℝ) ≤ stT228 52 := by
  have hc : ((-881547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1222486183797/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-881547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c53 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((758607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 887029/5000000) (δ := 723/62500000) (ψ := -261743/1000000) 228 144
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t53 : ((208391537597/2000000000000 : ℚ) : ℝ) ≤ stT228 53 := by
  have hc : ((758557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208391537597/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((758557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c54 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((128073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204963/625000) (δ := 573/50000000) (ψ := -261743/1000000) 228 145
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t54 : ((10890698481/312500000000 : ℚ) : ℝ) ≤ stT228 54 := by
  have hc : ((8003/31250 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10890698481/312500000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((8003/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c55 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-192767/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7179579/10000000) (δ := 573/50000000) (ψ := -261743/1000000) 228 145
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t55 : ((-649851267/5000000000 : ℚ) : ℝ) ≤ stT228 55 := by
  have hc : ((-192777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-649851267/5000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-192777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c56 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((383429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1742161/10000000) (δ := 229/20000000) (ψ := -261743/1000000) 228 146
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t56 : ((64043133203/625000000000 : ℚ) : ℝ) ≤ stT228 56 := by
  have hc : ((95851/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64043133203/625000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((95851/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c57 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((19983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387703/1000000) (δ := 11557/1000000000) (ψ := -261743/1000000) 228 147
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t57 : ((6600474089/2500000000000 : ℚ) : ℝ) ≤ stT228 57 := by
  have hc : ((19933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6600474089/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((19933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c58 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-373561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 754537/1250000) (δ := 11557/1000000000) (ψ := -261743/1000000) 228 147
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t58 : ((-49054270109/500000000000 : ℚ) : ℝ) ≤ stT228 58 := by
  have hc : ((-186793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49054270109/500000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-186793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c59 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((31237/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3607/500000) (δ := 11539/1000000000) (ψ := -261743/1000000) 228 148
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t59 : ((650641159863/5000000000000 : ℚ) : ℝ) ≤ stT228 59 := by
  have hc : ((499767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650641159863/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((499767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c60 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-752279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189243/312500) (δ := 1429/125000000) (ψ := -261743/1000000) 228 149
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t60 : ((-194250595471/2000000000000 : ℚ) : ℝ) ≤ stT228 60 := by
  have hc : ((-752329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194250595471/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-752329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c61 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((222547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134637/400000) (δ := 1429/125000000) (ψ := -261743/1000000) 228 149
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t61 : ((17804877431/625000000000 : ℚ) : ℝ) ≤ stT228 61 := by
  have hc : ((222497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17804877431/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((222497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c62 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((334783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3073553/10000000) (δ := 5739/500000000) (ψ := -261743/1000000) 228 150
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t62 : ((425111244733/10000000000000 : ℚ) : ℝ) ≤ stT228 62 := by
  have hc : ((334733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((425111244733/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((334733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c63 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-5999/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 241867/400000) (δ := 5739/500000000) (ψ := -261743/1000000) 228 150
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t63 : ((-18896340177/200000000000 : ℚ) : ℝ) ≤ stT228 63 := by
  have hc : ((-29997/40000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18896340177/200000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-29997/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c64 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((962723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -684757/10000000) (δ := 5793/500000000) (ψ := -261743/1000000) 228 151
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t64 : ((962673/8000000 : ℚ) : ℝ) ≤ stT228 64 := by
  have hc : ((962673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((962673/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((962673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c65 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-992873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7555327/10000000) (δ := 1151/100000000) (ψ := -261743/1000000) 228 152
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t65 : ((-307892514301/2500000000000 : ℚ) : ℝ) ≤ stT228 65 := by
  have hc : ((-992923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307892514301/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-992923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c66 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((448279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 286787/2500000) (δ := 1151/100000000) (ψ := -261743/1000000) 228 152
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t66 : ((137940531039/1250000000000 : ℚ) : ℝ) ≤ stT228 66 := by
  have hc : ((224127/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137940531039/1250000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((224127/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c67 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-91809/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1497303/2500000) (δ := 11403/1000000000) (ψ := -261743/1000000) 228 153
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t67 : ((-89736185479/1000000000000 : ℚ) : ℝ) ≤ stT228 67 := by
  have hc : ((-367261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89736185479/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-367261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c68 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((555229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 491079/2000000) (δ := 11403/1000000000) (ψ := -261743/1000000) 228 153
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t68 : ((336626679681/5000000000000 : ℚ) : ℝ) ≤ stT228 68 := by
  have hc : ((555179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336626679681/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((555179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c69 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-97747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1232813/2500000) (δ := 11507/1000000000) (ψ := -261743/1000000) 228 154
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t69 : ((-235377307821/5000000000000 : ℚ) : ℝ) ≤ stT228 69 := by
  have hc : ((-195519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235377307821/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-195519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c70 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((259663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3270307/10000000) (δ := 11507/1000000000) (ψ := -261743/1000000) 228 154
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t70 : ((77574181691/2500000000000 : ℚ) : ℝ) ≤ stT228 70 := by
  have hc : ((259613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77574181691/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((259613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c71 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-169357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -870487/2000000) (δ := 11589/1000000000) (ψ := -261743/1000000) 228 155
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t71 : ((-100524589137/5000000000000 : ℚ) : ℝ) ≤ stT228 71 := by
  have hc : ((-169407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100524589137/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-169407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c72 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((24517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904939/2500000) (δ := 11589/1000000000) (ψ := -261743/1000000) 228 155
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t72 : ((28881769077/2000000000000 : ℚ) : ℝ) ≤ stT228 72 := by
  have hc : ((24507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28881769077/2000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((24507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c73 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-119329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2113013/5000000) (δ := 11481/1000000000) (ψ := -261743/1000000) 228 156
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t73 : ((-34930653537/2500000000000 : ℚ) : ℝ) ≤ stT228 73 := by
  have hc : ((-119379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34930653537/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-119379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c74 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((158459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1764583/5000000) (δ := 11481/1000000000) (ψ := -261743/1000000) 228 156
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t74 : ((46036665171/2500000000000 : ℚ) : ℝ) ≤ stT228 74 := by
  have hc : ((158409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46036665171/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((158409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c75 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-237951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452763/1000000) (δ := 11429/1000000000) (ψ := -261743/1000000) 228 157
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t75 : ((-274819992701/10000000000000 : ℚ) : ℝ) ≤ stT228 75 := by
  have hc : ((-238001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274819992701/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-238001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c76 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((88523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1511067/5000000) (δ := 11429/1000000000) (ψ := -261743/1000000) 228 157
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t76 : ((101528447319/2500000000000 : ℚ) : ℝ) ≤ stT228 76 := by
  have hc : ((177021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101528447319/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((177021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c77 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-99913/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1308683/2500000) (δ := 721/62500000) (ψ := -261743/1000000) 228 158
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t77 : ((-56936425169/1000000000000 : ℚ) : ℝ) ≤ stT228 77 := by
  have hc : ((-99923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56936425169/1000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-99923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c78 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((661423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1060103/5000000) (δ := 721/62500000) (ψ := -261743/1000000) 228 158
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t78 : ((748857436321/10000000000000 : ℚ) : ℝ) ≤ stT228 78 := by
  have hc : ((661373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((748857436321/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((661373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c79 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-163817/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -49426/78125) (δ := 289/25000000) (ψ := -261743/1000000) 228 159
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t79 : ((-5759993493/62500000000 : ℚ) : ℝ) ≤ stT228 79 := by
  have hc : ((-163827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5759993493/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-163827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c80 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((943633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210847/2500000) (δ := 289/25000000) (ψ := -261743/1000000) 228 159
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t80 : ((1054956932239/10000000000000 : ℚ) : ℝ) ≤ stT228 80 := by
  have hc : ((943583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1054956932239/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((943583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c81 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-199921/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6227/8000) (δ := 11453/1000000000) (ψ := -261743/1000000) 228 160
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t81 : ((-27768216659/250000000000 : ℚ) : ℝ) ≤ stT228 81 := by
  have hc : ((-199931/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27768216659/250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-199931/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c82 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((59407/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789793/10000000) (δ := 11453/1000000000) (ψ := -261743/1000000) 228 160
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t82 : ((104960944353/1000000000000 : ℚ) : ℝ) ≤ stT228 82 := by
  have hc : ((475231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104960944353/1000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((475231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c83 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-384401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1223881/2000000) (δ := 11453/1000000000) (ψ := -261743/1000000) 228 160
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t83 : ((-210981253959/2500000000000 : ℚ) : ℝ) ≤ stT228 83 := by
  have hc : ((-192213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210981253959/2500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-192213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c84 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((224629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2762153/10000000) (δ := 11473/500000000) (ψ := -261743/1000000) 228 161
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t84 : ((61265738439/1250000000000 : ℚ) : ℝ) ≤ stT228 84 := by
  have hc : ((56151/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61265738439/1250000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((56151/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c85 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-4519/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 995871/2500000) (δ := 11457/1000000000) (ψ := -261743/1000000) 228 161
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t85 : ((-4912393437/2000000000000 : ℚ) : ℝ) ≤ stT228 85 := by
  have hc : ((-4529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4912393437/2000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-4529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c86 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-218521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5057759/10000000) (δ := 2313/200000000) (ψ := -261743/1000000) 228 162
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t86 : ((-14729016943/312500000000 : ℚ) : ℝ) ≤ stT228 86 := by
  have hc : ((-109273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14729016943/312500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-109273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c87 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((818051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 765977/5000000) (δ := 2313/200000000) (ψ := -261743/1000000) 228 162
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t87 : ((54811793007/625000000000 : ℚ) : ℝ) ≤ stT228 87 := by
  have hc : ((818001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54811793007/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((818001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c88 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-498521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7661651/10000000) (δ := 11531/1000000000) (ψ := -261743/1000000) 228 163
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t88 : ((-66431503773/625000000000 : ℚ) : ℝ) ≤ stT228 88 := by
  have hc : ((-249273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66431503773/625000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-249273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c89 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((883097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -152617/1250000) (δ := 11531/1000000000) (ψ := -261743/1000000) 228 163
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t89 : ((936027170859/10000000000000 : ℚ) : ℝ) ≤ stT228 89 := by
  have hc : ((883047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((936027170859/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((883047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c90 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-234581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1029569/2000000) (δ := 11531/1000000000) (ψ := -261743/1000000) 228 163
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t90 : ((-123648271179/2500000000000 : ℚ) : ℝ) ≤ stT228 90 := by
  have hc : ((-117303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123648271179/2500000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-117303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c91 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-26697/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4261703/10000000) (δ := 22979/1000000000) (ψ := -261743/1000000) 228 164
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t91 : ((-5599309499/400000000000 : ℚ) : ℝ) ≤ stT228 91 := by
  have hc : ((-26707/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5599309499/400000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-26707/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c92 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((705873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393571/2000000) (δ := 357/31250000) (ψ := -261743/1000000) 228 164
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t92 : ((183967824189/2500000000000 : ℚ) : ℝ) ≤ stT228 92 := by
  have hc : ((705823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183967824189/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((705823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c93 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-248477/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1515579/2000000) (δ := 5743/500000000) (ψ := -261743/1000000) 228 165
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t93 : ((-64417921001/625000000000 : ℚ) : ℝ) ≤ stT228 93 := by
  have hc : ((-496979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64417921001/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-496979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c94 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((33179/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -740787/5000000) (δ := 5743/500000000) (ψ := -261743/1000000) 228 165
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t94 : ((34219454517/400000000000 : ℚ) : ℝ) ≤ stT228 94 := by
  have hc : ((33177/40000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34219454517/400000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((33177/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c95 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-246719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4550223/10000000) (δ := 5743/500000000) (ψ := -261743/1000000) 228 165
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t95 : ((-253179811851/10000000000000 : ℚ) : ℝ) ≤ stT228 95 := by
  have hc : ((-246769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253179811851/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-246769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c96 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-48367/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5189099/10000000) (δ := 11593/1000000000) (ψ := -261743/1000000) 228 166
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t96 : ((-12342369753/250000000000 : ℚ) : ℝ) ≤ stT228 96 := by
  have hc : ((-12093/25000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12342369753/250000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-12093/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c97 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((38363/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 717697/10000000) (δ := 11593/1000000000) (ψ := -261743/1000000) 228 166
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t97 : ((19474843953/200000000000 : ℚ) : ℝ) ≤ stT228 97 := by
  have hc : ((38361/40000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19474843953/200000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((38361/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c98 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-108723/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3281951/5000000) (δ := 11593/1000000000) (ψ := -261743/1000000) 228 166
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t98 : ((-439332712301/5000000000000 : ℚ) : ℝ) ≤ stT228 98 := by
  have hc : ((-434917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439332712301/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-434917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c99 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((225951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1678597/5000000) (δ := 11503/1000000000) (ψ := -261743/1000000) 228 167
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t99 : ((227038863337/10000000000000 : ℚ) : ℝ) ≤ stT228 99 := by
  have hc : ((225901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227038863337/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((225901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c100 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((582829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2371477/10000000) (δ := 11503/1000000000) (ψ := -261743/1000000) 228 167
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t100 : ((582778417221/10000000000000 : ℚ) : ℝ) ≤ stT228 100 := by
  have hc : ((582779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((582778417221/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((582779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c101 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-997137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3832379/5000000) (δ := 713/62500000) (ψ := -261743/1000000) 228 168
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t101 : ((-496119479053/5000000000000 : ℚ) : ℝ) ≤ stT228 101 := by
  have hc : ((-997187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-496119479053/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-997187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c102 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((682529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2048947/10000000) (δ := 713/62500000) (ψ := -261743/1000000) 228 168
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t102 : ((675754534413/10000000000000 : ℚ) : ℝ) ≤ stT228 102 := by
  have hc : ((682479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((675754534413/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((682479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c103 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((165223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 351203/1000000) (δ := 713/62500000) (ψ := -261743/1000000) 228 168
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t103 : ((162749746917/10000000000000 : ℚ) : ℝ) ≤ stT228 103 := by
  have hc : ((165173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162749746917/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((165173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c104 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-893313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133773/200000) (δ := 2303/200000000) (ψ := -261743/1000000) 228 169
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t104 : ((-876014783903/10000000000000 : ℚ) : ℝ) ≤ stT228 104 := by
  have hc : ((-893363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-876014783903/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-893363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c105 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((440313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246807/2000000) (δ := 2303/200000000) (ψ := -261743/1000000) 228 169
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t105 : ((134274081/1562500000 : ℚ) : ℝ) ≤ stT228 105 := by
  have hc : ((13759/15625 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134274081/1562500000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((13759/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c106 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-48291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 521103/1250000) (δ := 2303/200000000) (ψ := -261743/1000000) 228 169
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t106 : ((-5866081797/625000000000 : ℚ) : ℝ) ≤ stT228 106 := by
  have hc : ((-12079/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5866081797/625000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-12079/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c107 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-392899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3093477/5000000) (δ := 11581/1000000000) (ψ := -261743/1000000) 228 170
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t107 : ((-94963542247/1250000000000 : ℚ) : ℝ) ≤ stT228 107 := by
  have hc : ((-98231/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94963542247/1250000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-98231/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c108 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((938051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -442293/5000000) (δ := 11581/1000000000) (ψ := -261743/1000000) 228 170
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t108 : ((3610365849/40000000000 : ℚ) : ℝ) ≤ stT228 108 := by
  have hc : ((938001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3610365849/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((938001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c109 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-35167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1092219/2500000) (δ := 11581/1000000000) (ψ := -261743/1000000) 228 170
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t109 : ((-33693480379/2000000000000 : ℚ) : ℝ) ≤ stT228 109 := by
  have hc : ((-35177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33693480379/2000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-35177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c110 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-772411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3066781/5000000) (δ := 5737/500000000) (ψ := -261743/1000000) 228 171
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t110 : ((-736512982443/10000000000000 : ℚ) : ℝ) ≤ stT228 110 := by
  have hc : ((-772461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-736512982443/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-772461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c111 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((924891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -975119/10000000) (δ := 5737/500000000) (ψ := -261743/1000000) 228 171
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t111 : ((877819309037/10000000000000 : ℚ) : ℝ) ≤ stT228 111 := by
  have hc : ((924841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((877819309037/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((924841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c112 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-41949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4136983/10000000) (δ := 5737/500000000) (ψ := -261743/1000000) 228 171
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t112 : ((-1239429259/156250000000 : ℚ) : ℝ) ≤ stT228 112 := by
  have hc : ((-20987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1239429259/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-20987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c113 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-214441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26017/40000) (δ := 2859/250000000) (ψ := -261743/1000000) 228 172
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t113 : ((-403481821947/5000000000000 : ℚ) : ℝ) ≤ stT228 113 := by
  have hc : ((-428907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403481821947/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-428907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c114 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((829333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46319/312500) (δ := 2859/250000000) (ψ := -261743/1000000) 228 172
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t114 : ((155338803711/2000000000000 : ℚ) : ℝ) ≤ stT228 114 := by
  have hc : ((829283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155338803711/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((829283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c115 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((171543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3496001/10000000) (δ := 2859/250000000) (ψ := -261743/1000000) 228 172
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t115 : ((19989738559/1250000000000 : ℚ) : ℝ) ≤ stT228 115 := by
  have hc : ((171493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19989738559/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((171493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c116 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-243369/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3638451/5000000) (δ := 1443/125000000) (ψ := -261743/1000000) 228 173
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t116 : ((-451948249951/5000000000000 : ℚ) : ℝ) ≤ stT228 116 := by
  have hc : ((-486763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451948249951/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-486763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c117 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((578707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298017/1250000) (δ := 1443/125000000) (ψ := -261743/1000000) 228 173
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t117 : ((1069936793/20000000000 : ℚ) : ℝ) ≤ stT228 117 := by
  have hc : ((578657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1069936793/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((578657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c118 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((4411/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2466963/10000000) (δ := 1443/125000000) (ψ := -261743/1000000) 228 173
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t118 : ((10150709211/200000000000 : ℚ) : ℝ) ≤ stT228 118 := by
  have hc : ((22053/40000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10150709211/200000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((22053/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c119 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-973493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7277079/10000000) (δ := 1443/125000000) (ψ := -261743/1000000) 228 173
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t119 : ((-892445894557/10000000000000 : ℚ) : ℝ) ≤ stT228 119 := by
  have hc : ((-973543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-892445894557/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-973543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c120 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((53107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1830477/5000000) (δ := 361/31250000) (ψ := -261743/1000000) 228 174
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t120 : ((2422848267/250000000000 : ℚ) : ℝ) ≤ stT228 120 := by
  have hc : ((26541/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2422848267/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((26541/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c121 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((56869/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534681/5000000) (δ := 361/31250000) (ψ := -261743/1000000) 228 174
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t121 : ((41356958643/500000000000 : ℚ) : ℝ) ≤ stT228 121 := by
  have hc : ((454927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41356958643/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((454927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c122 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-26779/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5760747/10000000) (δ := 361/31250000) (ψ := -261743/1000000) 228 174
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t122 : ((-12123196299/200000000000 : ℚ) : ℝ) ≤ stT228 122 := by
  have hc : ((-26781/40000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12123196299/200000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-26781/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c123 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-260003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1058827/2000000) (δ := 2289/200000000) (ψ := -261743/1000000) 228 175
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t123 : ((-5861486169/125000000000 : ℚ) : ℝ) ≤ stT228 123 := by
  have hc : ((-65007/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5861486169/125000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-65007/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c124 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((240843/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -678731/10000000) (δ := 2289/200000000) (ψ := -261743/1000000) 228 175
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t124 : ((216272050593/2500000000000 : ℚ) : ℝ) ≤ stT228 124 := by
  have hc : ((481661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216272050593/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((481661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c125 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((10947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3899623/10000000) (δ := 2289/200000000) (ψ := -261743/1000000) 228 175
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t125 : ((9746571019/10000000000000 : ℚ) : ℝ) ≤ stT228 125 := by
  have hc : ((10897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9746571019/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((10897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c126 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-972513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3633233/5000000) (δ := 2293/200000000) (ψ := -261743/1000000) 228 176
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t126 : ((-866428172373/10000000000000 : ℚ) : ℝ) ≤ stT228 126 := by
  have hc : ((-972563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866428172373/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-972563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c127 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((112457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2760559/10000000) (δ := 2293/200000000) (ψ := -261743/1000000) 228 176
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t127 : ((49889150871/1250000000000 : ℚ) : ℝ) ≤ stT228 127 := by
  have hc : ((224889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49889150871/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((224889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c128 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((155007/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 342013/2000000) (δ := 2293/200000000) (ψ := -261743/1000000) 228 176
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t128 : ((136999213351/2000000000000 : ℚ) : ℝ) ≤ stT228 128 := by
  have hc : ((154997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136999213351/2000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((154997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c129 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-775541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6145919/10000000) (δ := 2293/200000000) (ψ := -261743/1000000) 228 176
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t129 : ((-682869871541/10000000000000 : ℚ) : ℝ) ≤ stT228 129 := by
  have hc : ((-775591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682869871541/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-775591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c130 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-118407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -645063/1250000) (δ := 2893/250000000) (ψ := -261743/1000000) 228 177
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t130 : ((-207721776501/5000000000000 : ℚ) : ℝ) ≤ stT228 130 := by
  have hc : ((-236839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207721776501/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-236839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c131 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((237539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -792651/10000000) (δ := 2893/250000000) (ψ := -261743/1000000) 228 177
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t131 : ((51881963289/625000000000 : ℚ) : ℝ) ≤ stT228 131 := by
  have hc : ((475053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51881963289/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((475053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c132 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((767/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3541971/10000000) (δ := 2893/250000000) (ψ := -261743/1000000) 228 177
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t132 : ((667369999/50000000000 : ℚ) : ℝ) ≤ stT228 132 := by
  have hc : ((3067/20000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667369999/50000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((3067/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c133 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62751/80000) (δ := 2893/250000000) (ψ := -261743/1000000) 228 177
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t133 : ((-43357320931/500000000000 : ℚ) : ℝ) ≤ stT228 133 := by
  have hc : ((-500021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43357320931/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-500021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c134 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((132637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1797209/5000000) (δ := 22879/1000000000) (ψ := -261743/1000000) 228 178
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t134 : ((28634416629/2500000000000 : ℚ) : ℝ) ≤ stT228 134 := by
  have hc : ((132587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28634416629/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((132587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c135 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((193411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 643503/10000000) (δ := 2881/250000000) (ψ := -261743/1000000) 228 178
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t135 : ((83226445731/1000000000000 : ℚ) : ℝ) ≤ stT228 135 := by
  have hc : ((193401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83226445731/1000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((193401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c136 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-360933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60627/125000) (δ := 2881/250000000) (ψ := -261743/1000000) 228 178
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t136 : ((-309540395619/10000000000000 : ℚ) : ℝ) ≤ stT228 136 := by
  have hc : ((-360983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309540395619/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-360983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c137 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-892101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3340963/5000000) (δ := 1427/125000000) (ψ := -261743/1000000) 228 179
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t137 : ((-381108172029/5000000000000 : ℚ) : ℝ) ≤ stT228 137 := by
  have hc : ((-892151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381108172029/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-892151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c138 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((131991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2536487/10000000) (δ := 1427/125000000) (ψ := -261743/1000000) 228 179
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t138 : ((28086872499/625000000000 : ℚ) : ℝ) ≤ stT228 138 := by
  have hc : ((263957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28086872499/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((263957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c139 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((100883/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 394771/2500000) (δ := 1427/125000000) (ψ := -261743/1000000) 228 179
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t139 : ((85562448829/1250000000000 : ℚ) : ℝ) ≤ stT228 139 := by
  have hc : ((403507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85562448829/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((403507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c140 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-640581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5665129/10000000) (δ := 1427/125000000) (ψ := -261743/1000000) 228 179
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t140 : ((-108286498561/2000000000000 : ℚ) : ℝ) ≤ stT228 140 := by
  have hc : ((-640631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108286498561/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-640631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c141 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-733577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1496479/2500000) (δ := 5747/500000000) (ψ := -261743/1000000) 228 180
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t141 : ((-77228180663/1250000000000 : ℚ) : ℝ) ≤ stT228 141 := by
  have hc : ((-733627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77228180663/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-733627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c142 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((708769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489403/2500000) (δ := 5747/500000000) (ψ := -261743/1000000) 228 180
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t142 : ((594743519139/10000000000000 : ℚ) : ℝ) ≤ stT228 142 := by
  have hc : ((708719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594743519139/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((708719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c143 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((136887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102121/500000) (δ := 5747/500000000) (ψ := -261743/1000000) 228 180
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t143 : ((57231148117/1000000000000 : ℚ) : ℝ) ≤ stT228 143 := by
  have hc : ((136877/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57231148117/1000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((136877/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c144 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-148261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3007261/5000000) (δ := 5747/500000000) (ψ := -261743/1000000) 228 180
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t144 : ((-61779632757/1000000000000 : ℚ) : ℝ) ≤ stT228 144 := by
  have hc : ((-148271/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61779632757/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-148271/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c145 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-133181/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1437189/2500000) (δ := 11601/1000000000) (ψ := -261743/1000000) 228 181
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t145 : ((-22121826381/400000000000 : ℚ) : ℝ) ≤ stT228 145 := by
  have hc : ((-133191/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22121826381/400000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-133191/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c146 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((743517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1831203/10000000) (δ := 11601/1000000000) (ψ := -261743/1000000) 228 181
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t146 : ((123059401307/2000000000000 : ℚ) : ℝ) ≤ stT228 146 := by
  have hc : ((743467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123059401307/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((743467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c147 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((33971/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51489/250000) (δ := 11601/1000000000) (ψ := -261743/1000000) 228 181
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t147 : ((28016743241/500000000000 : ℚ) : ℝ) ≤ stT228 147 := by
  have hc : ((67937/100000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28016743241/500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((67937/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c148 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-716519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5923989/10000000) (δ := 11601/1000000000) (ψ := -261743/1000000) 228 181
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t148 : ((-117803227031/2000000000000 : ℚ) : ℝ) ≤ stT228 148 := by
  have hc : ((-716569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117803227031/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-716569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c149 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-144501/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2972769/5000000) (δ := 2299/200000000) (ψ := -261743/1000000) 228 182
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t149 : ((-3699626111/62500000000 : ℚ) : ℝ) ≤ stT228 149 := by
  have hc : ((-144511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3699626111/62500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-144511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c150 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((41101/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426573/2000000) (δ := 2299/200000000) (ψ := -261743/1000000) 228 182
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t150 : ((16778125273/312500000000 : ℚ) : ℝ) ≤ stT228 150 := by
  have hc : ((328783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16778125273/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((328783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c151 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((788873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1654557/10000000) (δ := 2299/200000000) (ψ := -261743/1000000) 228 182
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t151 : ((160483672881/2500000000000 : ℚ) : ℝ) ≤ stT228 151 := by
  have hc : ((788823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160483672881/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((788823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c152 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-22453/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1354239/2500000) (δ := 2299/200000000) (ψ := -261743/1000000) 228 182
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t152 : ((-910671507/20000000000 : ℚ) : ℝ) ≤ stT228 152 := by
  have hc : ((-4491/8000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-910671507/20000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-4491/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c153 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-867681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6553289/10000000) (δ := 2283/200000000) (ψ := -261743/1000000) 228 183
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t153 : ((-701519730143/10000000000000 : ℚ) : ℝ) ≤ stT228 153 := by
  have hc : ((-867731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-701519730143/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-867731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c154 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((210629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283991/1000000) (δ := 2283/200000000) (ψ := -261743/1000000) 228 183
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t154 : ((21213667061/625000000000 : ℚ) : ℝ) ≤ stT228 154 := by
  have hc : ((52651/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21213667061/625000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((52651/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c155 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((942833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169883/2000000) (δ := 2283/200000000) (ψ := -261743/1000000) 228 183
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t155 : ((757261218477/10000000000000 : ℚ) : ℝ) ≤ stT228 155 := by
  have hc : ((942783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((757261218477/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((942783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c156 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-58263/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1128757/2500000) (δ := 2283/200000000) (ψ := -261743/1000000) 228 183
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t156 : ((-93315509191/5000000000000 : ℚ) : ℝ) ≤ stT228 156 := by
  have hc : ((-116551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93315509191/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-116551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c157 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-992653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7550749/10000000) (δ := 11523/1000000000) (ψ := -261743/1000000) 228 184
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t157 : ((-792263359161/10000000000000 : ℚ) : ℝ) ≤ stT228 157 := by
  have hc : ((-992703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-792263359161/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-992703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c158 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -786341/2000000) (δ := 11523/1000000000) (ψ := -261743/1000000) 228 184
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t158 : ((-48131259/312500000000 : ℚ) : ℝ) ≤ stT228 158 := by
  have hc : ((-121/62500 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48131259/312500000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-121/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c159 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((991011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335461/10000000) (δ := 11523/1000000000) (ψ := -261743/1000000) 228 184
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t159 : ((785882612011/10000000000000 : ℚ) : ℝ) ≤ stT228 159 := by
  have hc : ((990961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((785882612011/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((990961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c160 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((6801/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3238211/10000000) (δ := 11523/1000000000) (ψ := -261743/1000000) 228 184
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t160 : ((21502686231/1000000000000 : ℚ) : ℝ) ≤ stT228 160 := by
  have hc : ((27199/100000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21502686231/1000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((27199/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c161 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-910727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1697399/2500000) (δ := 11523/1000000000) (ψ := -261743/1000000) 228 184
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t161 : ((-717793372247/10000000000000 : ℚ) : ℝ) ≤ stT228 161 := by
  have hc : ((-910777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-717793372247/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-910777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c162 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-138003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42101/78125) (δ := 11573/1000000000) (ψ := -261743/1000000) 228 185
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t162 : ((-8674826237/200000000000 : ℚ) : ℝ) ≤ stT228 162 := by
  have hc : ((-276031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8674826237/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-276031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c163 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((145999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -376241/2000000) (δ := 11573/1000000000) (ψ := -261743/1000000) 228 185
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t163 : ((5717367207/100000000000 : ℚ) : ℝ) ≤ stT228 163 := by
  have hc : ((145989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5717367207/100000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((145989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c164 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((800893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1605029/10000000) (δ := 11573/1000000000) (ψ := -261743/1000000) 228 185
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t164 : ((156338167931/2500000000000 : ℚ) : ℝ) ≤ stT228 164 := by
  have hc : ((800843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156338167931/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((800843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c165 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-220731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5070059/10000000) (δ := 11573/1000000000) (ψ := -261743/1000000) 228 185
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t165 : ((-42964581311/1250000000000 : ℚ) : ℝ) ≤ stT228 165 := by
  have hc : ((-55189/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42964581311/1250000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-55189/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c166 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-482667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7193793/10000000) (δ := 5733/500000000) (ψ := -261743/1000000) 228 186
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t166 : ((-93660469623/1250000000000 : ℚ) : ℝ) ≤ stT228 166 := by
  have hc : ((-120673/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93660469623/1250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-120673/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c167 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((62629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -942579/2500000) (δ := 5733/500000000) (ψ := -261743/1000000) 228 186
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t167 : ((48425069517/10000000000000 : ℚ) : ℝ) ≤ stT228 167 := by
  have hc : ((62579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48425069517/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((62579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c168 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((989223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367359/10000000) (δ := 5733/500000000) (ψ := -261743/1000000) 228 186
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t168 : ((190790699067/2500000000000 : ℚ) : ℝ) ≤ stT228 168 := by
  have hc : ((989173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190790699067/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((989173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c169 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((356581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3015477/10000000) (δ := 5733/500000000) (ψ := -261743/1000000) 228 186
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t169 : ((27425434113/1000000000000 : ℚ) : ℝ) ≤ stT228 169 := by
  have hc : ((356531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27425434113/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((356531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c170 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-83079/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3189153/5000000) (δ := 5733/500000000) (ψ := -261743/1000000) 228 186
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t170 : ((-3186126003/50000000000 : ℚ) : ℝ) ≤ stT228 170 := by
  have hc : ((-20771/25000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3186126003/50000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-20771/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c171 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-733749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119731/200000) (δ := 2861/250000000) (ψ := -261743/1000000) 228 187
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t171 : ((-7014384641/125000000000 : ℚ) : ℝ) ≤ stT228 171 := by
  have hc : ((-733799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7014384641/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-733799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c172 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((484351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2662937/10000000) (δ := 2861/250000000) (ψ := -261743/1000000) 228 187
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t172 : ((92318909523/2500000000000 : ℚ) : ℝ) ≤ stT228 172 := by
  have hc : ((484301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92318909523/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((484301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c173 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((241817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64141/1000000) (δ := 2861/250000000) (ψ := -261743/1000000) 228 187
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t173 : ((73536133713/1000000000000 : ℚ) : ℝ) ≤ stT228 173 := by
  have hc : ((483609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73536133713/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((483609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c174 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3926719/10000000) (δ := 2861/250000000) (ψ := -261743/1000000) 228 187
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t174 : ((22363891/5000000000000 : ℚ) : ℝ) ≤ stT228 174 := by
  have hc : ((59/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22363891/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((59/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c175 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-482637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3596609/5000000) (δ := 2861/250000000) (ψ := -261743/1000000) 228 187
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t175 : ((-182429101499/2500000000000 : ℚ) : ℝ) ≤ stT228 175 := by
  have hc : ((-241331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182429101499/2500000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-241331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c176 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-102133/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053377/2000000) (δ := 11551/1000000000) (ψ := -261743/1000000) 228 188
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t176 : ((-76993248397/2000000000000 : ℚ) : ℝ) ≤ stT228 176 := by
  have hc : ((-102143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76993248397/2000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-102143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c177 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((42869/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2037379/10000000) (δ := 11551/1000000000) (ψ := -261743/1000000) 228 188
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t177 : ((128879853921/2500000000000 : ℚ) : ℝ) ≤ stT228 177 := by
  have hc : ((342927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128879853921/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((342927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c178 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((89177/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1173887/10000000) (δ := 11551/1000000000) (ψ := -261743/1000000) 228 188
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t178 : ((16709294583/250000000000 : ℚ) : ℝ) ≤ stT228 178 := by
  have hc : ((22293/25000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16709294583/250000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((22293/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c179 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-87587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2183599/5000000) (δ := 11551/1000000000) (ψ := -261743/1000000) 228 188
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t179 : ((-4092772677/312500000000 : ℚ) : ℝ) ≤ stT228 179 := by
  have hc : ((-21903/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4092772677/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-21903/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c180 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-992257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1885667/2500000) (δ := 11551/1000000000) (ψ := -261743/1000000) 228 188
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t180 : ((-184905494073/2500000000000 : ℚ) : ℝ) ≤ stT228 180 := by
  have hc : ((-992307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184905494073/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-992307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c181 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-41883/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2503691/5000000) (δ := 2309/200000000) (ψ := -261743/1000000) 228 189
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t181 : ((-194594631/6250000000 : ℚ) : ℝ) ≤ stT228 181 := by
  have hc : ((-1309/3125 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194594631/6250000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-1309/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c182 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((733891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186691/1000000) (δ := 2309/200000000) (ψ := -261743/1000000) 228 189
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t182 : ((543958907409/10000000000000 : ℚ) : ℝ) ≤ stT228 182 := by
  have hc : ((733841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((543958907409/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((733841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c183 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((876351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251281/2000000) (δ := 2309/200000000) (ψ := -261743/1000000) 228 189
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t183 : ((647780101521/10000000000000 : ℚ) : ℝ) ≤ stT228 183 := by
  have hc : ((876301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((647780101521/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((876301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c184 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-86697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4362677/10000000) (δ := 2309/200000000) (ψ := -261743/1000000) 228 189
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t184 : ((-3196616281/250000000000 : ℚ) : ℝ) ≤ stT228 184 := by
  have hc : ((-43361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3196616281/250000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-43361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c185 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-987109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3726067/5000000) (δ := 2309/200000000) (ψ := -261743/1000000) 228 189
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t185 : ((-145154820837/2000000000000 : ℚ) : ℝ) ≤ stT228 185 := by
  have hc : ((-987159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145154820837/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-987159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c186 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-481559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5183073/10000000) (δ := 11437/1000000000) (ψ := -261743/1000000) 228 190
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t186 : ((-88283264181/2500000000000 : ℚ) : ℝ) ≤ stT228 186 := by
  have hc : ((-481609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88283264181/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-481609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c187 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((329731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2126733/10000000) (δ := 11437/1000000000) (ψ := -261743/1000000) 228 190
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t187 : ((15069047877/312500000000 : ℚ) : ℝ) ≤ stT228 187 := by
  have hc : ((164853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15069047877/312500000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((164853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c188 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((934017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28539/312500) (δ := 11437/1000000000) (ψ := -261743/1000000) 228 190
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t188 : ((170291137077/2500000000000 : ℚ) : ℝ) ≤ stT228 188 := by
  have hc : ((933967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170291137077/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((933967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c189 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-2033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 787431/2000000) (δ := 11437/1000000000) (ψ := -261743/1000000) 228 190
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t189 : ((-748487397/2500000000000 : ℚ) : ℝ) ≤ stT228 189 := by
  have hc : ((-1029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-748487397/2500000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-1029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c190 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-116829/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1389009/2000000) (δ := 11437/1000000000) (ψ := -261743/1000000) 228 190
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t190 : ((-339045146657/5000000000000 : ℚ) : ℝ) ≤ stT228 190 := by
  have hc : ((-467341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339045146657/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-467341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c191 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-134489/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144269/250000) (δ := 11473/1000000000) (ψ := -261743/1000000) 228 191
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t191 : ((-3892804557/80000000000 : ℚ) : ℝ) ≤ stT228 191 := by
  have hc : ((-134499/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3892804557/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-134499/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c192 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((218871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2794277/10000000) (δ := 11473/1000000000) (ψ := -261743/1000000) 228 191
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t192 : ((78969156601/2500000000000 : ℚ) : ℝ) ≤ stT228 192 := by
  have hc : ((109423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78969156601/2500000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((109423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c193 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((62361/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166759/10000000) (δ := 11473/1000000000) (ψ := -261743/1000000) 228 191
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t193 : ((71817814069/1000000000000 : ℚ) : ℝ) ≤ stT228 193 := by
  have hc : ((498863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71817814069/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((498863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c194 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((40007/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3112519/10000000) (δ := 11473/1000000000) (ψ := -261743/1000000) 228 191
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t194 : ((57437716937/2500000000000 : ℚ) : ℝ) ≤ stT228 194 := by
  have hc : ((160003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57437716937/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((160003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c195 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-748933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6043117/10000000) (δ := 11473/1000000000) (ψ := -261743/1000000) 228 191
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t195 : ((-107271592209/2000000000000 : ℚ) : ℝ) ≤ stT228 195 := by
  have hc : ((-748983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107271592209/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-748983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c196 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-451971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6749239/10000000) (δ := 579/50000000) (ψ := -261743/1000000) 228 192
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t196 : ((-40356801857/625000000000 : ℚ) : ℝ) ≤ stT228 196 := by
  have hc : ((-112999/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40356801857/625000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-112999/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c197 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((3141/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962113/2500000) (δ := 579/50000000) (ψ := -261743/1000000) 228 192
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t197 : ((3491103/1562500000 : ℚ) : ℝ) ≤ stT228 197 := by
  have hc : ((98/3125 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3491103/1562500000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((98/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c198 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((463409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962371/10000000) (δ := 579/50000000) (ψ := -261743/1000000) 228 192
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t198 : ((41164080487/625000000000 : ℚ) : ℝ) ≤ stT228 198 := by
  have hc : ((57923/62500 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41164080487/625000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((57923/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c199 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((722303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76367/400000) (δ := 579/50000000) (ψ := -261743/1000000) 228 192
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t199 : ((511991428893/10000000000000 : ℚ) : ℝ) ≤ stT228 199 := by
  have hc : ((722253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((511991428893/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((722253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c200 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-329453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47663/100000) (δ := 579/50000000) (ψ := -261743/1000000) 228 192
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t200 : ((-232993877821/10000000000000 : ℚ) : ℝ) ≤ stT228 200 := by
  have hc : ((-329503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232993877821/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-329503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c201 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-248803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 475577/625000) (δ := 579/50000000) (ψ := -261743/1000000) 228 192
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t201 : ((-175501017663/2500000000000 : ℚ) : ℝ) ≤ stT228 201 := by
  have hc : ((-497631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175501017663/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-497631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c202 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-511733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5269993/10000000) (δ := 2879/250000000) (ψ := -261743/1000000) 228 193
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t202 : ((-180044747617/5000000000000 : ℚ) : ℝ) ≤ stT228 202 := by
  have hc : ((-511783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180044747617/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-511783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c203 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((555307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1227581/5000000) (δ := 2879/250000000) (ψ := -261743/1000000) 228 193
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t203 : ((194856894267/5000000000000 : ℚ) : ℝ) ≤ stT228 203 := by
  have hc : ((555257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194856894267/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((555257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c204 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((61903/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172909/5000000) (δ := 2879/250000000) (ψ := -261743/1000000) 228 193
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t204 : ((17335431393/250000000000 : ℚ) : ℝ) ≤ stT228 204 := by
  have hc : ((495199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17335431393/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((495199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c205 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((312239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1566559/5000000) (δ := 2879/250000000) (ψ := -261743/1000000) 228 193
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t205 : ((21804216327/1000000000000 : ℚ) : ℝ) ≤ stT228 205 := by
  have hc : ((312189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21804216327/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((312189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c206 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-711721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1476713/2500000) (δ := 2879/250000000) (ψ := -261743/1000000) 228 193
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t206 : ((-247957527957/5000000000000 : ℚ) : ℝ) ≤ stT228 206 := by
  have hc : ((-711771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247957527957/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-711771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c207 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-947567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7040829/10000000) (δ := 11409/1000000000) (ψ := -261743/1000000) 228 194
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t207 : ((-658640248233/10000000000000 : ℚ) : ℝ) ≤ stT228 207 := by
  have hc : ((-947617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658640248233/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-947617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c208 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-146209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1073457/2500000) (δ := 11409/1000000000) (ψ := -261743/1000000) 228 194
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t208 : ((-792285003/78125000000 : ℚ) : ℝ) ≤ stT228 208 := by
  have hc : ((-146259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-792285003/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-146259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c209 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((811549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779997/5000000) (δ := 11409/1000000000) (ψ := -261743/1000000) 228 194
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t209 : ((280662609643/5000000000000 : ℚ) : ℝ) ≤ stT228 209 := by
  have hc : ((811499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280662609643/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((811499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c210 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((894129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1160787/10000000) (δ := 11409/1000000000) (ψ := -261743/1000000) 228 194
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t210 : ((123394525027/2000000000000 : ℚ) : ℝ) ≤ stT228 210 := by
  have hc : ((894079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123394525027/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((894079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c211 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((23343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3868629/10000000) (δ := 11409/1000000000) (ψ := -261743/1000000) 228 194
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t211 : ((4008888351/2500000000000 : ℚ) : ℝ) ≤ stT228 211 := by
  have hc : ((23293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4008888351/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((23293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c212 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-434867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3281823/5000000) (δ := 11409/1000000000) (ψ := -261743/1000000) 228 194
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t212 : ((-74671282569/1250000000000 : ℚ) : ℝ) ≤ stT228 212 := by
  have hc : ((-108723/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74671282569/1250000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-108723/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c213 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-169789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3230977/5000000) (δ := 5751/500000000) (ψ := -261743/1000000) 228 195
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t213 : ((-116344407011/2000000000000 : ℚ) : ℝ) ≤ stT228 213 := by
  have hc : ((-169799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116344407011/2000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-169799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c214 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((26959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3792131/10000000) (δ := 5751/500000000) (ψ := -261743/1000000) 228 195
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t214 : ((1841167839/500000000000 : ℚ) : ℝ) ≤ stT228 214 := by
  have hc : ((13467/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1841167839/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((13467/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c215 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((898737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1134791/10000000) (δ := 5751/500000000) (ψ := -261743/1000000) 228 195
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t215 : ((306449570939/5000000000000 : ℚ) : ℝ) ≤ stT228 215 := by
  have hc : ((898687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306449570939/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((898687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c216 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((823017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1510237/10000000) (δ := 5751/500000000) (ψ := -261743/1000000) 228 195
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t216 : ((559957445371/10000000000000 : ℚ) : ℝ) ≤ stT228 216 := by
  have hc : ((822967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((559957445371/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((822967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c217 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-863/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414301/1000000) (δ := 5751/500000000) (ψ := -261743/1000000) 228 195
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t217 : ((-234473063/40000000000 : ℚ) : ℝ) ≤ stT228 217 := by
  have hc : ((-1727/20000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234473063/40000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-1727/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c218 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-1133/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6763699/10000000) (δ := 5751/500000000) (ψ := -261743/1000000) 228 195
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t218 : ((-6139258947/100000000000 : ℚ) : ℝ) ≤ stT228 218 := by
  have hc : ((-18129/20000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6139258947/100000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-18129/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c219 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-821149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3167773/5000000) (δ := 5797/500000000) (ψ := -261743/1000000) 228 196
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t219 : ((-277457684931/5000000000000 : ℚ) : ℝ) ≤ stT228 219 := by
  have hc : ((-821199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277457684931/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-821199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c220 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((75229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186937/500000) (δ := 5797/500000000) (ψ := -261743/1000000) 228 196
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t220 : ((50685606621/10000000000000 : ℚ) : ℝ) ≤ stT228 220 := by
  have hc : ((75179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50685606621/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((75179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c221 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((895399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288419/2500000) (δ := 5797/500000000) (ψ := -261743/1000000) 228 196
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t221 : ((18821131329/312500000000 : ℚ) : ℝ) ≤ stT228 221 := by
  have hc : ((895349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18821131329/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((895349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c222 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((168611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 709823/5000000) (δ := 5797/500000000) (ψ := -261743/1000000) 228 196
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t222 : ((28289393189/500000000000 : ℚ) : ℝ) ≤ stT228 222 := by
  have hc : ((168601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28289393189/500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((168601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c223 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-2723/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1990727/5000000) (δ := 5797/500000000) (ψ := -261743/1000000) 228 196
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t223 : ((-146211381/100000000000 : ℚ) : ℝ) ≤ stT228 223 := by
  have hc : ((-10917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146211381/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-10917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c224 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-863377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1306361/2000000) (δ := 5797/500000000) (ψ := -261743/1000000) 228 196
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t224 : ((-288451101879/5000000000000 : ℚ) : ℝ) ≤ stT228 224 := by
  have hc : ((-863427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288451101879/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-863427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c225 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-441933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132743/200000) (δ := 11487/1000000000) (ψ := -261743/1000000) 228 197
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t225 : ((-147319406993/2500000000000 : ℚ) : ℝ) ≤ stT228 225 := by
  have hc : ((-220979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147319406993/2500000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-220979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c226 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-72921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256841/625000) (δ := 5729/250000000) (ψ := -261743/1000000) 228 197
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t226 : ((-48539652461/10000000000000 : ℚ) : ℝ) ≤ stT228 226 := by
  have hc : ((-72971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48539652461/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-72971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c227 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((401897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -796439/5000000) (δ := 11487/1000000000) (ψ := -261743/1000000) 228 197
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t227 : ((16670730591/312500000000 : ℚ) : ℝ) ≤ stT228 227 := by
  have hc : ((25117/31250 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16670730591/312500000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((25117/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c228 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((934107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 456307/5000000) (δ := 11487/1000000000) (ψ := -261743/1000000) 228 197
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t228 : ((309297096581/5000000000000 : ℚ) : ℝ) ≤ stT228 228 := by
  have hc : ((934057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309297096581/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((934057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c229 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((51609/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1703581/5000000) (δ := 11487/1000000000) (ψ := -261743/1000000) 228 197
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t229 : ((34095895937/2500000000000 : ℚ) : ℝ) ≤ stT228 229 := by
  have hc : ((103193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34095895937/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((103193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c230 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-353601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5890823/10000000) (δ := 11487/1000000000) (ψ := -261743/1000000) 228 197
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t230 : ((-116587132753/2500000000000 : ℚ) : ℝ) ≤ stT228 230 := by
  have hc : ((-176813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116587132753/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-176813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c231 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-489643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1836063/2500000) (δ := 11423/1000000000) (ψ := -261743/1000000) 228 198
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t231 : ((-2517015937/39062500000 : ℚ) : ℝ) ≤ stT228 231 := by
  have hc : ((-122417/125000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2517015937/39062500000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-122417/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c232 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-37281/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30513/62500) (δ := 11423/1000000000) (ψ := -261743/1000000) 228 198
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t232 : ((-12239744719/500000000000 : ℚ) : ℝ) ≤ stT228 232 := by
  have hc : ((-18643/50000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12239744719/500000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-18643/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c233 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((563499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2430453/10000000) (δ := 11423/1000000000) (ψ := -261743/1000000) 228 198
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t233 : ((369127272329/10000000000000 : ℚ) : ℝ) ≤ stT228 233 := by
  have hc : ((563449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369127272329/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((563449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c234 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((999991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5343/5000000) (δ := 11423/1000000000) (ψ := -261743/1000000) 228 198
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t234 : ((16342035763/250000000000 : ℚ) : ℝ) ≤ stT228 234 := by
  have hc : ((999941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16342035763/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((999941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c235 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((279939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1220697/5000000) (δ := 11423/1000000000) (ψ := -261743/1000000) 228 198
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t235 : ((11412233737/312500000000 : ℚ) : ℝ) ≤ stT228 235 := by
  have hc : ((139957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11412233737/312500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((139957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c236 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-73053/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 972357/2000000) (δ := 11423/1000000000) (ψ := -261743/1000000) 228 198
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t236 : ((-9511998907/400000000000 : ℚ) : ℝ) ≤ stT228 236 := by
  have hc : ((-73063/200000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9511998907/400000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-73063/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c237 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-486509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1817979/2500000) (δ := 11423/1000000000) (ψ := -261743/1000000) 228 198
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t237 : ((-15801894519/250000000000 : ℚ) : ℝ) ≤ stT228 237 := by
  have hc : ((-243267/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15801894519/250000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-243267/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c238 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-37353/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3018031/5000000) (δ := 1153/100000000) (ψ := -261743/1000000) 228 199
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t238 : ((-12106992261/250000000000 : ℚ) : ℝ) ≤ stT228 238 := by
  have hc : ((-74711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12106992261/250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-74711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c239 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((112117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3646109/10000000) (δ := 1153/100000000) (ψ := -261743/1000000) 228 199
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t239 : ((36245045341/5000000000000 : ℚ) : ℝ) ≤ stT228 239 := by
  have hc : ((112067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36245045341/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((112067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c240 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((874471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1266131/10000000) (δ := 1153/100000000) (ψ := -261743/1000000) 228 199
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t240 : ((564436132237/10000000000000 : ℚ) : ℝ) ≤ stT228 240 := by
  have hc : ((874421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((564436132237/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((874421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c241 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((904081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1103929/10000000) (δ := 1153/100000000) (ψ := -261743/1000000) 228 199
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t241 : ((145584248209/2500000000000 : ℚ) : ℝ) ≤ stT228 241 := by
  have hc : ((904031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145584248209/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((904031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c242 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((184067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 692837/2000000) (δ := 1153/100000000) (ψ := -261743/1000000) 228 199
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t242 : ((14786318001/1250000000000 : ℚ) : ℝ) ≤ stT228 242 := by
  have hc : ((184017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14786318001/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((184017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c243 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-171337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2907347/5000000) (δ := 1153/100000000) (ψ := -261743/1000000) 228 199
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t243 : ((-219841751199/5000000000000 : ℚ) : ℝ) ≤ stT228 243 := by
  have hc : ((-342699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219841751199/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-342699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c244 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-248183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3776197/5000000) (δ := 5783/500000000) (ψ := -261743/1000000) 228 200
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t244 : ((-63556414467/1000000000000 : ℚ) : ℝ) ≤ stT228 244 := by
  have hc : ((-496391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63556414467/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-496391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c245 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-247421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2610561/5000000) (δ := 22837/1000000000) (ψ := -261743/1000000) 228 200
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t245 : ((-79043779071/2500000000000 : ℚ) : ℝ) ≤ stT228 245 := by
  have hc : ((-123723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79043779071/2500000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-123723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c246 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((399591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2899313/10000000) (δ := 5783/500000000) (ψ := -261743/1000000) 228 200
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t246 : ((31842219077/1250000000000 : ℚ) : ℝ) ≤ stT228 246 := by
  have hc : ((399541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31842219077/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((399541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c247 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((972567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -586937/10000000) (δ := 5783/500000000) (ψ := -261743/1000000) 228 200
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t247 : ((154699251707/2500000000000 : ℚ) : ℝ) ≤ stT228 247 := by
  have hc : ((972517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154699251707/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((972517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c248 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((773509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1716091/10000000) (δ := 5783/500000000) (ψ := -261743/1000000) 228 200
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t248 : ((98229293/2000000000 : ℚ) : ℝ) ≤ stT228 248 := by
  have hc : ((773459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98229293/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((773459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c249 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-33129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1002457/2500000) (δ := 5783/500000000) (ψ := -261743/1000000) 228 200
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t249 : ((-841054471/400000000000 : ℚ) : ℝ) ≤ stT228 249 := by
  have hc : ((-33179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-841054471/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-33179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_c250 :
    |Real.cos (((228 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((-101457/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1258889/2000000) (δ := 5783/500000000) (ψ := -261743/1000000) 228 200
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st228_t250 : ((-32085520621/625000000000 : ℚ) : ℝ) ≤ stT228 250 := by
  have hc : ((-405853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((228 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st228_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32085520621/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-405853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st228_p1 : ((96589/100000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT228 (i+1) := by
  rw [Finset.sum_range_one]
  exact st228_t1

theorem st228_p2 : ((2418149201461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT228 (i+1))
      = (∑ i ∈ Finset.range 1, stT228 (i+1)) + stT228 2 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 1
    simpa using h
  have hprev := st228_p1
  have hstep := st228_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p3 : ((16913196343351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT228 (i+1))
      = (∑ i ∈ Finset.range 2, stT228 (i+1)) + stT228 3 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 2
    simpa using h
  have hprev := st228_p2
  have hstep := st228_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p4 : ((2812353154613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT228 (i+1))
      = (∑ i ∈ Finset.range 3, stT228 (i+1)) + stT228 4 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 3
    simpa using h
  have hprev := st228_p3
  have hstep := st228_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p5 : ((9864764524057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT228 (i+1))
      = (∑ i ∈ Finset.range 4, stT228 (i+1)) + stT228 5 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 4
    simpa using h
  have hprev := st228_p4
  have hstep := st228_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p6 : ((13662064743947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT228 (i+1))
      = (∑ i ∈ Finset.range 5, stT228 (i+1)) + stT228 6 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 5
    simpa using h
  have hprev := st228_p5
  have hstep := st228_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p7 : ((719295573387/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT228 (i+1))
      = (∑ i ∈ Finset.range 6, stT228 (i+1)) + stT228 7 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 6
    simpa using h
  have hprev := st228_p6
  have hstep := st228_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p8 : ((498317627319/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT228 (i+1))
      = (∑ i ∈ Finset.range 7, stT228 (i+1)) + stT228 8 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 7
    simpa using h
  have hprev := st228_p7
  have hstep := st228_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p9 : ((2113567163913/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT228 (i+1))
      = (∑ i ∈ Finset.range 8, stT228 (i+1)) + stT228 9 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 8
    simpa using h
  have hprev := st228_p8
  have hstep := st228_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p10 : ((1463355372943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT228 (i+1))
      = (∑ i ∈ Finset.range 9, stT228 (i+1)) + stT228 10 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 9
    simpa using h
  have hprev := st228_p9
  have hstep := st228_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p11 : ((4345493273827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT228 (i+1))
      = (∑ i ∈ Finset.range 10, stT228 (i+1)) + stT228 11 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 10
    simpa using h
  have hprev := st228_p10
  have hstep := st228_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p12 : ((4684328559203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT228 (i+1))
      = (∑ i ∈ Finset.range 11, stT228 (i+1)) + stT228 12 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 11
    simpa using h
  have hprev := st228_p11
  have hstep := st228_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p13 : ((5713958538953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT228 (i+1))
      = (∑ i ∈ Finset.range 12, stT228 (i+1)) + stT228 13 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 12
    simpa using h
  have hprev := st228_p12
  have hstep := st228_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p14 : ((246975952277/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT228 (i+1))
      = (∑ i ∈ Finset.range 13, stT228 (i+1)) + stT228 14 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 13
    simpa using h
  have hprev := st228_p13
  have hstep := st228_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p15 : ((11404773377659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT228 (i+1))
      = (∑ i ∈ Finset.range 14, stT228 (i+1)) + stT228 15 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 14
    simpa using h
  have hprev := st228_p14
  have hstep := st228_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p16 : ((2488553824359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT228 (i+1))
      = (∑ i ∈ Finset.range 15, stT228 (i+1)) + stT228 16 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 15
    simpa using h
  have hprev := st228_p15
  have hstep := st228_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p17 : ((569842550061/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT228 (i+1))
      = (∑ i ∈ Finset.range 16, stT228 (i+1)) + stT228 17 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 16
    simpa using h
  have hprev := st228_p16
  have hstep := st228_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p18 : ((843772276809/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT228 (i+1))
      = (∑ i ∈ Finset.range 17, stT228 (i+1)) + stT228 18 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 17
    simpa using h
  have hprev := st228_p17
  have hstep := st228_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p19 : ((15244514523921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT228 (i+1))
      = (∑ i ∈ Finset.range 18, stT228 (i+1)) + stT228 19 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 18
    simpa using h
  have hprev := st228_p18
  have hstep := st228_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p20 : ((15227171580513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT228 (i+1))
      = (∑ i ∈ Finset.range 19, stT228 (i+1)) + stT228 20 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 19
    simpa using h
  have hprev := st228_p19
  have hstep := st228_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p21 : ((2612161802781/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT228 (i+1))
      = (∑ i ∈ Finset.range 20, stT228 (i+1)) + stT228 21 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 20
    simpa using h
  have hprev := st228_p20
  have hstep := st228_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p22 : ((13625530764051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT228 (i+1))
      = (∑ i ∈ Finset.range 21, stT228 (i+1)) + stT228 22 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 21
    simpa using h
  have hprev := st228_p21
  have hstep := st228_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p23 : ((2903507320191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT228 (i+1))
      = (∑ i ∈ Finset.range 22, stT228 (i+1)) + stT228 23 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 22
    simpa using h
  have hprev := st228_p22
  have hstep := st228_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p24 : ((13170067849431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT228 (i+1))
      = (∑ i ∈ Finset.range 23, stT228 (i+1)) + stT228 24 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 23
    simpa using h
  have hprev := st228_p23
  have hstep := st228_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p25 : ((14305109849431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT228 (i+1))
      = (∑ i ∈ Finset.range 24, stT228 (i+1)) + stT228 25 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 24
    simpa using h
  have hprev := st228_p24
  have hstep := st228_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p26 : ((2813621468811/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT228 (i+1))
      = (∑ i ∈ Finset.range 25, stT228 (i+1)) + stT228 26 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 25
    simpa using h
  have hprev := st228_p25
  have hstep := st228_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p27 : ((3207459784283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT228 (i+1))
      = (∑ i ∈ Finset.range 26, stT228 (i+1)) + stT228 27 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 26
    simpa using h
  have hprev := st228_p26
  have hstep := st228_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p28 : ((3663885814079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT228 (i+1))
      = (∑ i ∈ Finset.range 27, stT228 (i+1)) + stT228 28 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 27
    simpa using h
  have hprev := st228_p27
  have hstep := st228_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p29 : ((14867066915593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT228 (i+1))
      = (∑ i ∈ Finset.range 28, stT228 (i+1)) + stT228 29 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 28
    simpa using h
  have hprev := st228_p28
  have hstep := st228_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p30 : ((2618595396503/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT228 (i+1))
      = (∑ i ∈ Finset.range 29, stT228 (i+1)) + stT228 30 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 29
    simpa using h
  have hprev := st228_p29
  have hstep := st228_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p31 : ((12054394388583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT228 (i+1))
      = (∑ i ∈ Finset.range 30, stT228 (i+1)) + stT228 31 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 30
    simpa using h
  have hprev := st228_p30
  have hstep := st228_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p32 : ((2528428952759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT228 (i+1))
      = (∑ i ∈ Finset.range 31, stT228 (i+1)) + stT228 32 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 31
    simpa using h
  have hprev := st228_p31
  have hstep := st228_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p33 : ((14170507794723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT228 (i+1))
      = (∑ i ∈ Finset.range 32, stT228 (i+1)) + stT228 33 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 32
    simpa using h
  have hprev := st228_p32
  have hstep := st228_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p34 : ((15884902839883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT228 (i+1))
      = (∑ i ∈ Finset.range 33, stT228 (i+1)) + stT228 34 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 33
    simpa using h
  have hprev := st228_p33
  have hstep := st228_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p35 : ((17472534770731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT228 (i+1))
      = (∑ i ∈ Finset.range 34, stT228 (i+1)) + stT228 35 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 34
    simpa using h
  have hprev := st228_p34
  have hstep := st228_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p36 : ((18943025849201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT228 (i+1))
      = (∑ i ∈ Finset.range 35, stT228 (i+1)) + stT228 36 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 35
    simpa using h
  have hprev := st228_p35
  have hstep := st228_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p37 : ((1276285573931/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT228 (i+1))
      = (∑ i ∈ Finset.range 36, stT228 (i+1)) + stT228 37 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 36
    simpa using h
  have hprev := st228_p36
  have hstep := st228_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p38 : ((10995949598179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT228 (i+1))
      = (∑ i ∈ Finset.range 37, stT228 (i+1)) + stT228 38 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 37
    simpa using h
  have hprev := st228_p37
  have hstep := st228_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p39 : ((23583449211721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT228 (i+1))
      = (∑ i ∈ Finset.range 38, stT228 (i+1)) + stT228 39 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 38
    simpa using h
  have hprev := st228_p38
  have hstep := st228_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p40 : ((24869697069031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT228 (i+1))
      = (∑ i ∈ Finset.range 39, stT228 (i+1)) + stT228 40 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 39
    simpa using h
  have hprev := st228_p39
  have hstep := st228_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p41 : ((12663295518533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT228 (i+1))
      = (∑ i ∈ Finset.range 40, stT228 (i+1)) + stT228 41 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 40
    simpa using h
  have hprev := st228_p40
  have hstep := st228_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p42 : ((491952494853/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT228 (i+1))
      = (∑ i ∈ Finset.range 41, stT228 (i+1)) + stT228 42 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 41
    simpa using h
  have hprev := st228_p41
  have hstep := st228_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p43 : ((11546091481613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT228 (i+1))
      = (∑ i ∈ Finset.range 42, stT228 (i+1)) + stT228 43 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 42
    simpa using h
  have hprev := st228_p42
  have hstep := st228_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p44 : ((4426544787809/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT228 (i+1))
      = (∑ i ∈ Finset.range 43, stT228 (i+1)) + stT228 44 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 43
    simpa using h
  have hprev := st228_p43
  have hstep := st228_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p45 : ((22807222963793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT228 (i+1))
      = (∑ i ∈ Finset.range 44, stT228 (i+1)) + stT228 45 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 44
    simpa using h
  have hprev := st228_p44
  have hstep := st228_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p46 : ((6065029230203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT228 (i+1))
      = (∑ i ∈ Finset.range 45, stT228 (i+1)) + stT228 46 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 45
    simpa using h
  have hprev := st228_p45
  have hstep := st228_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p47 : ((24289594758453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT228 (i+1))
      = (∑ i ∈ Finset.range 46, stT228 (i+1)) + stT228 47 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 46
    simpa using h
  have hprev := st228_p46
  have hstep := st228_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p48 : ((22854562915109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT228 (i+1))
      = (∑ i ∈ Finset.range 47, stT228 (i+1)) + stT228 48 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 47
    simpa using h
  have hprev := st228_p47
  have hstep := st228_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p49 : ((22716371431261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT228 (i+1))
      = (∑ i ∈ Finset.range 48, stT228 (i+1)) + stT228 49 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 48
    simpa using h
  have hprev := st228_p48
  have hstep := st228_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p50 : ((6032613227363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT228 (i+1))
      = (∑ i ∈ Finset.range 49, stT228 (i+1)) + stT228 50 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 49
    simpa using h
  have hprev := st228_p49
  have hstep := st228_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p51 : ((7450933257/3125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT228 (i+1))
      = (∑ i ∈ Finset.range 50, stT228 (i+1)) + stT228 51 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 50
    simpa using h
  have hprev := st228_p50
  have hstep := st228_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p52 : ((22620500238603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT228 (i+1))
      = (∑ i ∈ Finset.range 51, stT228 (i+1)) + stT228 52 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 51
    simpa using h
  have hprev := st228_p51
  have hstep := st228_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p53 : ((5915614481647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT228 (i+1))
      = (∑ i ∈ Finset.range 52, stT228 (i+1)) + stT228 53 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 52
    simpa using h
  have hprev := st228_p52
  have hstep := st228_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p54 : ((1200548013899/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT228 (i+1))
      = (∑ i ∈ Finset.range 53, stT228 (i+1)) + stT228 54 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 53
    simpa using h
  have hprev := st228_p53
  have hstep := st228_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p55 : ((1135562887199/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT228 (i+1))
      = (∑ i ∈ Finset.range 54, stT228 (i+1)) + stT228 55 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 54
    simpa using h
  have hprev := st228_p54
  have hstep := st228_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p56 : ((5933986968807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT228 (i+1))
      = (∑ i ∈ Finset.range 55, stT228 (i+1)) + stT228 56 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 55
    simpa using h
  have hprev := st228_p55
  have hstep := st228_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p57 : ((371286715181/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT228 (i+1))
      = (∑ i ∈ Finset.range 56, stT228 (i+1)) + stT228 57 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 56
    simpa using h
  have hprev := st228_p56
  have hstep := st228_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p58 : ((5695316092351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT228 (i+1))
      = (∑ i ∈ Finset.range 57, stT228 (i+1)) + stT228 58 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 57
    simpa using h
  have hprev := st228_p57
  have hstep := st228_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p59 : ((2408254668913/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT228 (i+1))
      = (∑ i ∈ Finset.range 58, stT228 (i+1)) + stT228 59 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 58
    simpa using h
  have hprev := st228_p58
  have hstep := st228_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p60 : ((924451748471/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT228 (i+1))
      = (∑ i ∈ Finset.range 59, stT228 (i+1)) + stT228 60 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 59
    simpa using h
  have hprev := st228_p59
  have hstep := st228_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p61 : ((23396171750671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT228 (i+1))
      = (∑ i ∈ Finset.range 60, stT228 (i+1)) + stT228 61 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 60
    simpa using h
  have hprev := st228_p60
  have hstep := st228_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p62 : ((5955320748851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT228 (i+1))
      = (∑ i ∈ Finset.range 61, stT228 (i+1)) + stT228 62 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 61
    simpa using h
  have hprev := st228_p61
  have hstep := st228_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p63 : ((11438232993277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT228 (i+1))
      = (∑ i ∈ Finset.range 62, stT228 (i+1)) + stT228 63 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 62
    simpa using h
  have hprev := st228_p62
  have hstep := st228_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p64 : ((12039903618277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT228 (i+1))
      = (∑ i ∈ Finset.range 63, stT228 (i+1)) + stT228 64 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 63
    simpa using h
  have hprev := st228_p63
  have hstep := st228_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p65 : ((456964743587/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT228 (i+1))
      = (∑ i ∈ Finset.range 64, stT228 (i+1)) + stT228 65 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 64
    simpa using h
  have hprev := st228_p64
  have hstep := st228_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p66 : ((11975880713831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT228 (i+1))
      = (∑ i ∈ Finset.range 65, stT228 (i+1)) + stT228 66 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 65
    simpa using h
  have hprev := st228_p65
  have hstep := st228_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p67 : ((2881799946609/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT228 (i+1))
      = (∑ i ∈ Finset.range 66, stT228 (i+1)) + stT228 67 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 66
    simpa using h
  have hprev := st228_p66
  have hstep := st228_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p68 : ((11863826466117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT228 (i+1))
      = (∑ i ∈ Finset.range 67, stT228 (i+1)) + stT228 68 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 67
    simpa using h
  have hprev := st228_p67
  have hstep := st228_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p69 : ((1453556144787/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT228 (i+1))
      = (∑ i ∈ Finset.range 68, stT228 (i+1)) + stT228 69 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 68
    simpa using h
  have hprev := st228_p68
  have hstep := st228_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p70 : ((5891798760839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT228 (i+1))
      = (∑ i ∈ Finset.range 69, stT228 (i+1)) + stT228 70 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 69
    simpa using h
  have hprev := st228_p69
  have hstep := st228_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p71 : ((11683072932541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT228 (i+1))
      = (∑ i ∈ Finset.range 70, stT228 (i+1)) + stT228 71 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 70
    simpa using h
  have hprev := st228_p70
  have hstep := st228_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p72 : ((23510554710467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT228 (i+1))
      = (∑ i ∈ Finset.range 71, stT228 (i+1)) + stT228 72 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 71
    simpa using h
  have hprev := st228_p71
  have hstep := st228_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p73 : ((23370832096319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT228 (i+1))
      = (∑ i ∈ Finset.range 72, stT228 (i+1)) + stT228 73 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 72
    simpa using h
  have hprev := st228_p72
  have hstep := st228_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p74 : ((23554978757003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT228 (i+1))
      = (∑ i ∈ Finset.range 73, stT228 (i+1)) + stT228 74 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 73
    simpa using h
  have hprev := st228_p73
  have hstep := st228_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p75 : ((11640079382151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT228 (i+1))
      = (∑ i ∈ Finset.range 74, stT228 (i+1)) + stT228 75 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 74
    simpa using h
  have hprev := st228_p74
  have hstep := st228_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p76 : ((11843136276789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT228 (i+1))
      = (∑ i ∈ Finset.range 75, stT228 (i+1)) + stT228 76 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 75
    simpa using h
  have hprev := st228_p75
  have hstep := st228_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p77 : ((361201692217/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT228 (i+1))
      = (∑ i ∈ Finset.range 76, stT228 (i+1)) + stT228 77 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 76
    simpa using h
  have hprev := st228_p76
  have hstep := st228_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p78 : ((23865765738209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT228 (i+1))
      = (∑ i ∈ Finset.range 77, stT228 (i+1)) + stT228 78 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 77
    simpa using h
  have hprev := st228_p77
  have hstep := st228_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p79 : ((22944166779329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT228 (i+1))
      = (∑ i ∈ Finset.range 78, stT228 (i+1)) + stT228 79 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 78
    simpa using h
  have hprev := st228_p78
  have hstep := st228_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p80 : ((1499945231973/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT228 (i+1))
      = (∑ i ∈ Finset.range 79, stT228 (i+1)) + stT228 80 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 79
    simpa using h
  have hprev := st228_p79
  have hstep := st228_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p81 : ((2861049380651/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT228 (i+1))
      = (∑ i ∈ Finset.range 80, stT228 (i+1)) + stT228 81 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 80
    simpa using h
  have hprev := st228_p80
  have hstep := st228_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p82 : ((11969002244369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT228 (i+1))
      = (∑ i ∈ Finset.range 81, stT228 (i+1)) + stT228 82 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 81
    simpa using h
  have hprev := st228_p81
  have hstep := st228_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p83 : ((11547039736451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT228 (i+1))
      = (∑ i ∈ Finset.range 82, stT228 (i+1)) + stT228 83 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 82
    simpa using h
  have hprev := st228_p82
  have hstep := st228_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p84 : ((11792102690207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT228 (i+1))
      = (∑ i ∈ Finset.range 83, stT228 (i+1)) + stT228 84 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 83
    simpa using h
  have hprev := st228_p83
  have hstep := st228_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p85 : ((23559643413229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT228 (i+1))
      = (∑ i ∈ Finset.range 84, stT228 (i+1)) + stT228 85 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 84
    simpa using h
  have hprev := st228_p84
  have hstep := st228_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p86 : ((23088314871053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT228 (i+1))
      = (∑ i ∈ Finset.range 85, stT228 (i+1)) + stT228 86 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 85
    simpa using h
  have hprev := st228_p85
  have hstep := st228_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p87 : ((4793060711833/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT228 (i+1))
      = (∑ i ∈ Finset.range 86, stT228 (i+1)) + stT228 87 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 86
    simpa using h
  have hprev := st228_p86
  have hstep := st228_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p88 : ((22902399498797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT228 (i+1))
      = (∑ i ∈ Finset.range 87, stT228 (i+1)) + stT228 88 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 87
    simpa using h
  have hprev := st228_p87
  have hstep := st228_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p89 : ((2979803333707/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT228 (i+1))
      = (∑ i ∈ Finset.range 88, stT228 (i+1)) + stT228 89 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 88
    simpa using h
  have hprev := st228_p88
  have hstep := st228_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p90 : ((1167191679247/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT228 (i+1))
      = (∑ i ∈ Finset.range 89, stT228 (i+1)) + stT228 90 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 89
    simpa using h
  have hprev := st228_p89
  have hstep := st228_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p91 : ((4640770169493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT228 (i+1))
      = (∑ i ∈ Finset.range 90, stT228 (i+1)) + stT228 91 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 90
    simpa using h
  have hprev := st228_p90
  have hstep := st228_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p92 : ((23939722144221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT228 (i+1))
      = (∑ i ∈ Finset.range 91, stT228 (i+1)) + stT228 92 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 91
    simpa using h
  have hprev := st228_p91
  have hstep := st228_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p93 : ((4581807081641/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT228 (i+1))
      = (∑ i ∈ Finset.range 92, stT228 (i+1)) + stT228 93 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 92
    simpa using h
  have hprev := st228_p92
  have hstep := st228_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p94 : ((2376452177113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT228 (i+1))
      = (∑ i ∈ Finset.range 93, stT228 (i+1)) + stT228 94 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 93
    simpa using h
  have hprev := st228_p93
  have hstep := st228_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p95 : ((23511341959279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT228 (i+1))
      = (∑ i ∈ Finset.range 94, stT228 (i+1)) + stT228 95 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 94
    simpa using h
  have hprev := st228_p94
  have hstep := st228_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p96 : ((23017647169159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT228 (i+1))
      = (∑ i ∈ Finset.range 95, stT228 (i+1)) + stT228 96 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 95
    simpa using h
  have hprev := st228_p95
  have hstep := st228_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p97 : ((23991389366809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT228 (i+1))
      = (∑ i ∈ Finset.range 96, stT228 (i+1)) + stT228 97 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 96
    simpa using h
  have hprev := st228_p96
  have hstep := st228_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p98 : ((23112723942207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT228 (i+1))
      = (∑ i ∈ Finset.range 97, stT228 (i+1)) + stT228 98 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 97
    simpa using h
  have hprev := st228_p97
  have hstep := st228_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p99 : ((2917470350693/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT228 (i+1))
      = (∑ i ∈ Finset.range 98, stT228 (i+1)) + stT228 99 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 98
    simpa using h
  have hprev := st228_p98
  have hstep := st228_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p100 : ((4784508244553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT228 (i+1))
      = (∑ i ∈ Finset.range 99, stT228 (i+1)) + stT228 100 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 99
    simpa using h
  have hprev := st228_p99
  have hstep := st228_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p101 : ((22930302264659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT228 (i+1))
      = (∑ i ∈ Finset.range 100, stT228 (i+1)) + stT228 101 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 100
    simpa using h
  have hprev := st228_p100
  have hstep := st228_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p102 : ((737689274971/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT228 (i+1))
      = (∑ i ∈ Finset.range 101, stT228 (i+1)) + stT228 102 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 101
    simpa using h
  have hprev := st228_p101
  have hstep := st228_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p103 : ((23768806545989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT228 (i+1))
      = (∑ i ∈ Finset.range 102, stT228 (i+1)) + stT228 103 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 102
    simpa using h
  have hprev := st228_p102
  have hstep := st228_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p104 : ((11446395881043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT228 (i+1))
      = (∑ i ∈ Finset.range 103, stT228 (i+1)) + stT228 104 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 103
    simpa using h
  have hprev := st228_p103
  have hstep := st228_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p105 : ((11876072940243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT228 (i+1))
      = (∑ i ∈ Finset.range 104, stT228 (i+1)) + stT228 105 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 104
    simpa using h
  have hprev := st228_p104
  have hstep := st228_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p106 : ((11829144285867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT228 (i+1))
      = (∑ i ∈ Finset.range 105, stT228 (i+1)) + stT228 106 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 105
    simpa using h
  have hprev := st228_p105
  have hstep := st228_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p107 : ((11449290116879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT228 (i+1))
      = (∑ i ∈ Finset.range 106, stT228 (i+1)) + stT228 107 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 106
    simpa using h
  have hprev := st228_p106
  have hstep := st228_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p108 : ((2975146462001/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT228 (i+1))
      = (∑ i ∈ Finset.range 107, stT228 (i+1)) + stT228 108 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 107
    simpa using h
  have hprev := st228_p107
  have hstep := st228_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p109 : ((23632704294113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT228 (i+1))
      = (∑ i ∈ Finset.range 108, stT228 (i+1)) + stT228 109 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 108
    simpa using h
  have hprev := st228_p108
  have hstep := st228_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p110 : ((2289619131167/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT228 (i+1))
      = (∑ i ∈ Finset.range 109, stT228 (i+1)) + stT228 110 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 109
    simpa using h
  have hprev := st228_p109
  have hstep := st228_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p111 : ((23774010620707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT228 (i+1))
      = (∑ i ∈ Finset.range 110, stT228 (i+1)) + stT228 111 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 110
    simpa using h
  have hprev := st228_p110
  have hstep := st228_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p112 : ((23694687148131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT228 (i+1))
      = (∑ i ∈ Finset.range 111, stT228 (i+1)) + stT228 112 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 111
    simpa using h
  have hprev := st228_p111
  have hstep := st228_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p113 : ((22887723504237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT228 (i+1))
      = (∑ i ∈ Finset.range 112, stT228 (i+1)) + stT228 113 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 112
    simpa using h
  have hprev := st228_p112
  have hstep := st228_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p114 : ((2958052190349/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT228 (i+1))
      = (∑ i ∈ Finset.range 113, stT228 (i+1)) + stT228 114 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 113
    simpa using h
  have hprev := st228_p113
  have hstep := st228_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p115 : ((744510482227/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT228 (i+1))
      = (∑ i ∈ Finset.range 114, stT228 (i+1)) + stT228 115 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 114
    simpa using h
  have hprev := st228_p114
  have hstep := st228_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p116 : ((11460219465681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT228 (i+1))
      = (∑ i ∈ Finset.range 115, stT228 (i+1)) + stT228 116 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 115
    simpa using h
  have hprev := st228_p115
  have hstep := st228_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p117 : ((11727703663931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT228 (i+1))
      = (∑ i ∈ Finset.range 116, stT228 (i+1)) + stT228 117 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 116
    simpa using h
  have hprev := st228_p116
  have hstep := st228_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p118 : ((5990735697103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT228 (i+1))
      = (∑ i ∈ Finset.range 117, stT228 (i+1)) + stT228 118 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 117
    simpa using h
  have hprev := st228_p117
  have hstep := st228_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p119 : ((4614099378771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT228 (i+1))
      = (∑ i ∈ Finset.range 118, stT228 (i+1)) + stT228 119 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 118
    simpa using h
  have hprev := st228_p118
  have hstep := st228_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p120 : ((4633482164907/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT228 (i+1))
      = (∑ i ∈ Finset.range 119, stT228 (i+1)) + stT228 120 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 119
    simpa using h
  have hprev := st228_p119
  have hstep := st228_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p121 : ((4798909999479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT228 (i+1))
      = (∑ i ∈ Finset.range 120, stT228 (i+1)) + stT228 121 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 120
    simpa using h
  have hprev := st228_p120
  have hstep := st228_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p122 : ((4677678036489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT228 (i+1))
      = (∑ i ∈ Finset.range 121, stT228 (i+1)) + stT228 122 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 121
    simpa using h
  have hprev := st228_p121
  have hstep := st228_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p123 : ((916778851557/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT228 (i+1))
      = (∑ i ∈ Finset.range 122, stT228 (i+1)) + stT228 123 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 122
    simpa using h
  have hprev := st228_p122
  have hstep := st228_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p124 : ((23784559491297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT228 (i+1))
      = (∑ i ∈ Finset.range 123, stT228 (i+1)) + stT228 124 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 123
    simpa using h
  have hprev := st228_p123
  have hstep := st228_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p125 : ((5948576515579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT228 (i+1))
      = (∑ i ∈ Finset.range 124, stT228 (i+1)) + stT228 125 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 124
    simpa using h
  have hprev := st228_p124
  have hstep := st228_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p126 : ((22927877889943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT228 (i+1))
      = (∑ i ∈ Finset.range 125, stT228 (i+1)) + stT228 126 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 125
    simpa using h
  have hprev := st228_p125
  have hstep := st228_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p127 : ((23326991096911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT228 (i+1))
      = (∑ i ∈ Finset.range 126, stT228 (i+1)) + stT228 127 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 126
    simpa using h
  have hprev := st228_p126
  have hstep := st228_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p128 : ((12005993581833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT228 (i+1))
      = (∑ i ∈ Finset.range 127, stT228 (i+1)) + stT228 128 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 127
    simpa using h
  have hprev := st228_p127
  have hstep := st228_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p129 : ((186632938337/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT228 (i+1))
      = (∑ i ∈ Finset.range 128, stT228 (i+1)) + stT228 129 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 128
    simpa using h
  have hprev := st228_p128
  have hstep := st228_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p130 : ((22913673739123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT228 (i+1))
      = (∑ i ∈ Finset.range 129, stT228 (i+1)) + stT228 130 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 129
    simpa using h
  have hprev := st228_p129
  have hstep := st228_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p131 : ((23743785151747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT228 (i+1))
      = (∑ i ∈ Finset.range 130, stT228 (i+1)) + stT228 131 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 130
    simpa using h
  have hprev := st228_p130
  have hstep := st228_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p132 : ((23877259151547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT228 (i+1))
      = (∑ i ∈ Finset.range 131, stT228 (i+1)) + stT228 132 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 131
    simpa using h
  have hprev := st228_p131
  have hstep := st228_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p133 : ((23010112732927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT228 (i+1))
      = (∑ i ∈ Finset.range 132, stT228 (i+1)) + stT228 133 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 132
    simpa using h
  have hprev := st228_p132
  have hstep := st228_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p134 : ((23124650399443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT228 (i+1))
      = (∑ i ∈ Finset.range 133, stT228 (i+1)) + stT228 134 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 133
    simpa using h
  have hprev := st228_p133
  have hstep := st228_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p135 : ((23956914856753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT228 (i+1))
      = (∑ i ∈ Finset.range 134, stT228 (i+1)) + stT228 135 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 134
    simpa using h
  have hprev := st228_p134
  have hstep := st228_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p136 : ((11823687230567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT228 (i+1))
      = (∑ i ∈ Finset.range 135, stT228 (i+1)) + stT228 136 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 135
    simpa using h
  have hprev := st228_p135
  have hstep := st228_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p137 : ((5721289529269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT228 (i+1))
      = (∑ i ∈ Finset.range 136, stT228 (i+1)) + stT228 137 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 136
    simpa using h
  have hprev := st228_p136
  have hstep := st228_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p138 : ((1166727403853/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT228 (i+1))
      = (∑ i ∈ Finset.range 137, stT228 (i+1)) + stT228 138 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 137
    simpa using h
  have hprev := st228_p137
  have hstep := st228_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p139 : ((6004761916923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT228 (i+1))
      = (∑ i ∈ Finset.range 138, stT228 (i+1)) + stT228 139 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 138
    simpa using h
  have hprev := st228_p138
  have hstep := st228_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p140 : ((23477615174887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT228 (i+1))
      = (∑ i ∈ Finset.range 139, stT228 (i+1)) + stT228 140 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 139
    simpa using h
  have hprev := st228_p139
  have hstep := st228_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p141 : ((22859789729583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT228 (i+1))
      = (∑ i ∈ Finset.range 140, stT228 (i+1)) + stT228 141 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 140
    simpa using h
  have hprev := st228_p140
  have hstep := st228_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p142 : ((11727266624361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT228 (i+1))
      = (∑ i ∈ Finset.range 141, stT228 (i+1)) + stT228 142 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 141
    simpa using h
  have hprev := st228_p141
  have hstep := st228_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p143 : ((6006711182473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT228 (i+1))
      = (∑ i ∈ Finset.range 142, stT228 (i+1)) + stT228 143 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 142
    simpa using h
  have hprev := st228_p142
  have hstep := st228_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p144 : ((11704524201161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT228 (i+1))
      = (∑ i ∈ Finset.range 143, stT228 (i+1)) + stT228 144 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 143
    simpa using h
  have hprev := st228_p143
  have hstep := st228_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p145 : ((22856002742797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT228 (i+1))
      = (∑ i ∈ Finset.range 144, stT228 (i+1)) + stT228 145 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 144
    simpa using h
  have hprev := st228_p144
  have hstep := st228_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p146 : ((5867824937333/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT228 (i+1))
      = (∑ i ∈ Finset.range 145, stT228 (i+1)) + stT228 146 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 145
    simpa using h
  have hprev := st228_p145
  have hstep := st228_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p147 : ((3003954326769/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT228 (i+1))
      = (∑ i ∈ Finset.range 146, stT228 (i+1)) + stT228 147 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 146
    simpa using h
  have hprev := st228_p146
  have hstep := st228_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p148 : ((23442618478997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT228 (i+1))
      = (∑ i ∈ Finset.range 147, stT228 (i+1)) + stT228 148 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 147
    simpa using h
  have hprev := st228_p147
  have hstep := st228_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p149 : ((22850678301237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT228 (i+1))
      = (∑ i ∈ Finset.range 148, stT228 (i+1)) + stT228 149 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 148
    simpa using h
  have hprev := st228_p148
  have hstep := st228_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p150 : ((23387578309973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT228 (i+1))
      = (∑ i ∈ Finset.range 149, stT228 (i+1)) + stT228 150 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 149
    simpa using h
  have hprev := st228_p149
  have hstep := st228_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p151 : ((24029513001497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT228 (i+1))
      = (∑ i ∈ Finset.range 150, stT228 (i+1)) + stT228 151 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 150
    simpa using h
  have hprev := st228_p150
  have hstep := st228_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p152 : ((23574177247997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT228 (i+1))
      = (∑ i ∈ Finset.range 151, stT228 (i+1)) + stT228 152 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 151
    simpa using h
  have hprev := st228_p151
  have hstep := st228_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p153 : ((11436328758927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT228 (i+1))
      = (∑ i ∈ Finset.range 152, stT228 (i+1)) + stT228 153 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 152
    simpa using h
  have hprev := st228_p152
  have hstep := st228_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p154 : ((2321207619083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT228 (i+1))
      = (∑ i ∈ Finset.range 153, stT228 (i+1)) + stT228 154 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 153
    simpa using h
  have hprev := st228_p153
  have hstep := st228_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p155 : ((23969337409307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT228 (i+1))
      = (∑ i ∈ Finset.range 154, stT228 (i+1)) + stT228 155 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 154
    simpa using h
  have hprev := st228_p154
  have hstep := st228_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p156 : ((951308255637/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT228 (i+1))
      = (∑ i ∈ Finset.range 155, stT228 (i+1)) + stT228 156 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 155
    simpa using h
  have hprev := st228_p155
  have hstep := st228_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p157 : ((5747610757941/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT228 (i+1))
      = (∑ i ∈ Finset.range 156, stT228 (i+1)) + stT228 157 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 156
    simpa using h
  have hprev := st228_p156
  have hstep := st228_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p158 : ((5747225707869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT228 (i+1))
      = (∑ i ∈ Finset.range 157, stT228 (i+1)) + stT228 158 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 157
    simpa using h
  have hprev := st228_p157
  have hstep := st228_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p159 : ((23774785443487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT228 (i+1))
      = (∑ i ∈ Finset.range 158, stT228 (i+1)) + stT228 159 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 158
    simpa using h
  have hprev := st228_p158
  have hstep := st228_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p160 : ((23989812305797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT228 (i+1))
      = (∑ i ∈ Finset.range 159, stT228 (i+1)) + stT228 160 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 159
    simpa using h
  have hprev := st228_p159
  have hstep := st228_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p161 : ((465440378671/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT228 (i+1))
      = (∑ i ∈ Finset.range 160, stT228 (i+1)) + stT228 161 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 160
    simpa using h
  have hprev := st228_p160
  have hstep := st228_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p162 : ((228382776217/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT228 (i+1))
      = (∑ i ∈ Finset.range 161, stT228 (i+1)) + stT228 162 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 161
    simpa using h
  have hprev := st228_p161
  have hstep := st228_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p163 : ((3657814741/1562500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT228 (i+1))
      = (∑ i ∈ Finset.range 162, stT228 (i+1)) + stT228 163 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 162
    simpa using h
  have hprev := st228_p162
  have hstep := st228_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p164 : ((6008841753531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT228 (i+1))
      = (∑ i ∈ Finset.range 163, stT228 (i+1)) + stT228 164 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 163
    simpa using h
  have hprev := st228_p163
  have hstep := st228_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p165 : ((5922912590909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT228 (i+1))
      = (∑ i ∈ Finset.range 164, stT228 (i+1)) + stT228 165 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 164
    simpa using h
  have hprev := st228_p164
  have hstep := st228_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p166 : ((5735591651663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT228 (i+1))
      = (∑ i ∈ Finset.range 165, stT228 (i+1)) + stT228 166 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 165
    simpa using h
  have hprev := st228_p165
  have hstep := st228_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p167 : ((22990791676169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT228 (i+1))
      = (∑ i ∈ Finset.range 166, stT228 (i+1)) + stT228 167 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 166
    simpa using h
  have hprev := st228_p166
  have hstep := st228_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p168 : ((23753954472437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT228 (i+1))
      = (∑ i ∈ Finset.range 167, stT228 (i+1)) + stT228 168 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 167
    simpa using h
  have hprev := st228_p167
  have hstep := st228_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p169 : ((24028208813567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT228 (i+1))
      = (∑ i ∈ Finset.range 168, stT228 (i+1)) + stT228 169 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 168
    simpa using h
  have hprev := st228_p168
  have hstep := st228_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p170 : ((23390983612967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT228 (i+1))
      = (∑ i ∈ Finset.range 169, stT228 (i+1)) + stT228 170 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 169
    simpa using h
  have hprev := st228_p169
  have hstep := st228_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p171 : ((22829832841687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT228 (i+1))
      = (∑ i ∈ Finset.range 170, stT228 (i+1)) + stT228 171 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 170
    simpa using h
  have hprev := st228_p170
  have hstep := st228_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p172 : ((23199108479779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT228 (i+1))
      = (∑ i ∈ Finset.range 171, stT228 (i+1)) + stT228 172 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 171
    simpa using h
  have hprev := st228_p171
  have hstep := st228_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p173 : ((23934469816909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT228 (i+1))
      = (∑ i ∈ Finset.range 172, stT228 (i+1)) + stT228 173 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 172
    simpa using h
  have hprev := st228_p172
  have hstep := st228_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p174 : ((23934514544691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT228 (i+1))
      = (∑ i ∈ Finset.range 173, stT228 (i+1)) + stT228 174 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 173
    simpa using h
  have hprev := st228_p173
  have hstep := st228_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p175 : ((4640959627739/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT228 (i+1))
      = (∑ i ∈ Finset.range 174, stT228 (i+1)) + stT228 175 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 174
    simpa using h
  have hprev := st228_p174
  have hstep := st228_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p176 : ((2281983189671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT228 (i+1))
      = (∑ i ∈ Finset.range 175, stT228 (i+1)) + stT228 176 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 175
    simpa using h
  have hprev := st228_p175
  have hstep := st228_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p177 : ((11667675656197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT228 (i+1))
      = (∑ i ∈ Finset.range 176, stT228 (i+1)) + stT228 177 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 176
    simpa using h
  have hprev := st228_p176
  have hstep := st228_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p178 : ((12001861547857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT228 (i+1))
      = (∑ i ∈ Finset.range 177, stT228 (i+1)) + stT228 178 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 177
    simpa using h
  have hprev := st228_p177
  have hstep := st228_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p179 : ((477455087401/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT228 (i+1))
      = (∑ i ∈ Finset.range 178, stT228 (i+1)) + stT228 179 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 178
    simpa using h
  have hprev := st228_p178
  have hstep := st228_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p180 : ((11566566196879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT228 (i+1))
      = (∑ i ∈ Finset.range 179, stT228 (i+1)) + stT228 180 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 179
    simpa using h
  have hprev := st228_p179
  have hstep := st228_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p181 : ((11410890492079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT228 (i+1))
      = (∑ i ∈ Finset.range 180, stT228 (i+1)) + stT228 181 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 180
    simpa using h
  have hprev := st228_p180
  have hstep := st228_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p182 : ((23365739891567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT228 (i+1))
      = (∑ i ∈ Finset.range 181, stT228 (i+1)) + stT228 182 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 181
    simpa using h
  have hprev := st228_p181
  have hstep := st228_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p183 : ((93802812473/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT228 (i+1))
      = (∑ i ∈ Finset.range 182, stT228 (i+1)) + stT228 183 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 182
    simpa using h
  have hprev := st228_p182
  have hstep := st228_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p184 : ((2985706917731/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT228 (i+1))
      = (∑ i ∈ Finset.range 183, stT228 (i+1)) + stT228 184 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 183
    simpa using h
  have hprev := st228_p183
  have hstep := st228_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p185 : ((23159881237663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT228 (i+1))
      = (∑ i ∈ Finset.range 184, stT228 (i+1)) + stT228 185 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 184
    simpa using h
  have hprev := st228_p184
  have hstep := st228_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p186 : ((22806748180939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT228 (i+1))
      = (∑ i ∈ Finset.range 185, stT228 (i+1)) + stT228 186 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 185
    simpa using h
  have hprev := st228_p185
  have hstep := st228_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p187 : ((23288957713003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT228 (i+1))
      = (∑ i ∈ Finset.range 186, stT228 (i+1)) + stT228 187 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 186
    simpa using h
  have hprev := st228_p186
  have hstep := st228_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p188 : ((23970122261311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT228 (i+1))
      = (∑ i ∈ Finset.range 187, stT228 (i+1)) + stT228 188 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 187
    simpa using h
  have hprev := st228_p187
  have hstep := st228_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p189 : ((23967128311723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT228 (i+1))
      = (∑ i ∈ Finset.range 188, stT228 (i+1)) + stT228 189 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 188
    simpa using h
  have hprev := st228_p188
  have hstep := st228_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p190 : ((23289038018409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT228 (i+1))
      = (∑ i ∈ Finset.range 189, stT228 (i+1)) + stT228 190 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 189
    simpa using h
  have hprev := st228_p189
  have hstep := st228_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p191 : ((1425152340549/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT228 (i+1))
      = (∑ i ∈ Finset.range 190, stT228 (i+1)) + stT228 191 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 190
    simpa using h
  have hprev := st228_p190
  have hstep := st228_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p192 : ((5779578518797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT228 (i+1))
      = (∑ i ∈ Finset.range 191, stT228 (i+1)) + stT228 192 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 191
    simpa using h
  have hprev := st228_p191
  have hstep := st228_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p193 : ((11918246107939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT228 (i+1))
      = (∑ i ∈ Finset.range 192, stT228 (i+1)) + stT228 193 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 192
    simpa using h
  have hprev := st228_p192
  have hstep := st228_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p194 : ((12033121541813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT228 (i+1))
      = (∑ i ∈ Finset.range 193, stT228 (i+1)) + stT228 194 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 193
    simpa using h
  have hprev := st228_p193
  have hstep := st228_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p195 : ((23529885122581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT228 (i+1))
      = (∑ i ∈ Finset.range 194, stT228 (i+1)) + stT228 195 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 194
    simpa using h
  have hprev := st228_p194
  have hstep := st228_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p196 : ((22884176292869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT228 (i+1))
      = (∑ i ∈ Finset.range 195, stT228 (i+1)) + stT228 196 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 195
    simpa using h
  have hprev := st228_p195
  have hstep := st228_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p197 : ((22906519352069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT228 (i+1))
      = (∑ i ∈ Finset.range 196, stT228 (i+1)) + stT228 197 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 196
    simpa using h
  have hprev := st228_p196
  have hstep := st228_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p198 : ((23565144639861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT228 (i+1))
      = (∑ i ∈ Finset.range 197, stT228 (i+1)) + stT228 198 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 197
    simpa using h
  have hprev := st228_p197
  have hstep := st228_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p199 : ((12038568034377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT228 (i+1))
      = (∑ i ∈ Finset.range 198, stT228 (i+1)) + stT228 199 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 198
    simpa using h
  have hprev := st228_p198
  have hstep := st228_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p200 : ((23844142190933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT228 (i+1))
      = (∑ i ∈ Finset.range 199, stT228 (i+1)) + stT228 200 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 199
    simpa using h
  have hprev := st228_p199
  have hstep := st228_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p201 : ((23142138120281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT228 (i+1))
      = (∑ i ∈ Finset.range 200, stT228 (i+1)) + stT228 201 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 200
    simpa using h
  have hprev := st228_p200
  have hstep := st228_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p202 : ((22782048625047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT228 (i+1))
      = (∑ i ∈ Finset.range 201, stT228 (i+1)) + stT228 202 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 201
    simpa using h
  have hprev := st228_p201
  have hstep := st228_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p203 : ((23171762413581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT228 (i+1))
      = (∑ i ∈ Finset.range 202, stT228 (i+1)) + stT228 203 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 202
    simpa using h
  have hprev := st228_p202
  have hstep := st228_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p204 : ((23865179669301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT228 (i+1))
      = (∑ i ∈ Finset.range 203, stT228 (i+1)) + stT228 204 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 203
    simpa using h
  have hprev := st228_p203
  have hstep := st228_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p205 : ((24083221832571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT228 (i+1))
      = (∑ i ∈ Finset.range 204, stT228 (i+1)) + stT228 205 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 204
    simpa using h
  have hprev := st228_p204
  have hstep := st228_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p206 : ((23587306776657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT228 (i+1))
      = (∑ i ∈ Finset.range 205, stT228 (i+1)) + stT228 206 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 205
    simpa using h
  have hprev := st228_p205
  have hstep := st228_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p207 : ((2866083316053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT228 (i+1))
      = (∑ i ∈ Finset.range 206, stT228 (i+1)) + stT228 207 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 206
    simpa using h
  have hprev := st228_p206
  have hstep := st228_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p208 : ((570681351201/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT228 (i+1))
      = (∑ i ∈ Finset.range 207, stT228 (i+1)) + stT228 208 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 207
    simpa using h
  have hprev := st228_p207
  have hstep := st228_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p209 : ((11694289633663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT228 (i+1))
      = (∑ i ∈ Finset.range 208, stT228 (i+1)) + stT228 209 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 208
    simpa using h
  have hprev := st228_p208
  have hstep := st228_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p210 : ((24005551892461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT228 (i+1))
      = (∑ i ∈ Finset.range 209, stT228 (i+1)) + stT228 210 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 209
    simpa using h
  have hprev := st228_p209
  have hstep := st228_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p211 : ((4804317489173/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT228 (i+1))
      = (∑ i ∈ Finset.range 210, stT228 (i+1)) + stT228 211 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 210
    simpa using h
  have hprev := st228_p210
  have hstep := st228_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p212 : ((23424217185313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT228 (i+1))
      = (∑ i ∈ Finset.range 211, stT228 (i+1)) + stT228 212 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 211
    simpa using h
  have hprev := st228_p211
  have hstep := st228_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p213 : ((11421247575129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT228 (i+1))
      = (∑ i ∈ Finset.range 212, stT228 (i+1)) + stT228 213 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 212
    simpa using h
  have hprev := st228_p212
  have hstep := st228_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p214 : ((11439659253519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT228 (i+1))
      = (∑ i ∈ Finset.range 213, stT228 (i+1)) + stT228 214 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 213
    simpa using h
  have hprev := st228_p213
  have hstep := st228_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p215 : ((5873054412229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT228 (i+1))
      = (∑ i ∈ Finset.range 214, stT228 (i+1)) + stT228 215 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 214
    simpa using h
  have hprev := st228_p214
  have hstep := st228_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p216 : ((24052175094287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT228 (i+1))
      = (∑ i ∈ Finset.range 215, stT228 (i+1)) + stT228 216 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 215
    simpa using h
  have hprev := st228_p215
  have hstep := st228_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p217 : ((23993556828537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT228 (i+1))
      = (∑ i ∈ Finset.range 216, stT228 (i+1)) + stT228 217 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 216
    simpa using h
  have hprev := st228_p216
  have hstep := st228_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p218 : ((23379630933837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT228 (i+1))
      = (∑ i ∈ Finset.range 217, stT228 (i+1)) + stT228 218 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 217
    simpa using h
  have hprev := st228_p217
  have hstep := st228_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p219 : ((912988622559/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT228 (i+1))
      = (∑ i ∈ Finset.range 218, stT228 (i+1)) + stT228 219 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 218
    simpa using h
  have hprev := st228_p218
  have hstep := st228_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p220 : ((5718850292649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT228 (i+1))
      = (∑ i ∈ Finset.range 219, stT228 (i+1)) + stT228 220 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 219
    simpa using h
  have hprev := st228_p219
  have hstep := st228_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p221 : ((5869419343281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT228 (i+1))
      = (∑ i ∈ Finset.range 220, stT228 (i+1)) + stT228 221 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 220
    simpa using h
  have hprev := st228_p220
  have hstep := st228_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p222 : ((3005433154613/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT228 (i+1))
      = (∑ i ∈ Finset.range 221, stT228 (i+1)) + stT228 222 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 221
    simpa using h
  have hprev := st228_p221
  have hstep := st228_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p223 : ((6007211024701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT228 (i+1))
      = (∑ i ∈ Finset.range 222, stT228 (i+1)) + stT228 223 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 222
    simpa using h
  have hprev := st228_p222
  have hstep := st228_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p224 : ((11725970947523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT228 (i+1))
      = (∑ i ∈ Finset.range 223, stT228 (i+1)) + stT228 224 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 223
    simpa using h
  have hprev := st228_p223
  have hstep := st228_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p225 : ((11431332133537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT228 (i+1))
      = (∑ i ∈ Finset.range 224, stT228 (i+1)) + stT228 225 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 224
    simpa using h
  have hprev := st228_p224
  have hstep := st228_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p226 : ((22814124614613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT228 (i+1))
      = (∑ i ∈ Finset.range 225, stT228 (i+1)) + stT228 226 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 225
    simpa using h
  have hprev := st228_p225
  have hstep := st228_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p227 : ((933903519741/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT228 (i+1))
      = (∑ i ∈ Finset.range 226, stT228 (i+1)) + stT228 227 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 226
    simpa using h
  have hprev := st228_p226
  have hstep := st228_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p228 : ((23966182186687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT228 (i+1))
      = (∑ i ∈ Finset.range 227, stT228 (i+1)) + stT228 228 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 227
    simpa using h
  have hprev := st228_p227
  have hstep := st228_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p229 : ((4820513154087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT228 (i+1))
      = (∑ i ∈ Finset.range 228, stT228 (i+1)) + stT228 229 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 228
    simpa using h
  have hprev := st228_p228
  have hstep := st228_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p230 : ((23636217239423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT228 (i+1))
      = (∑ i ∈ Finset.range 229, stT228 (i+1)) + stT228 230 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 229
    simpa using h
  have hprev := st228_p229
  have hstep := st228_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p231 : ((22991861159551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT228 (i+1))
      = (∑ i ∈ Finset.range 230, stT228 (i+1)) + stT228 231 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 230
    simpa using h
  have hprev := st228_p230
  have hstep := st228_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p232 : ((22747066265171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT228 (i+1))
      = (∑ i ∈ Finset.range 231, stT228 (i+1)) + stT228 232 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 231
    simpa using h
  have hprev := st228_p231
  have hstep := st228_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p233 : ((1849295483/800000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT228 (i+1))
      = (∑ i ∈ Finset.range 232, stT228 (i+1)) + stT228 233 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 232
    simpa using h
  have hprev := st228_p232
  have hstep := st228_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p234 : ((1188493748401/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT228 (i+1))
      = (∑ i ∈ Finset.range 233, stT228 (i+1)) + stT228 234 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 233
    simpa using h
  have hprev := st228_p233
  have hstep := st228_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p235 : ((6033766611901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT228 (i+1))
      = (∑ i ∈ Finset.range 234, stT228 (i+1)) + stT228 235 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 234
    simpa using h
  have hprev := st228_p234
  have hstep := st228_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p236 : ((23897266474929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT228 (i+1))
      = (∑ i ∈ Finset.range 235, stT228 (i+1)) + stT228 236 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 235
    simpa using h
  have hprev := st228_p235
  have hstep := st228_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p237 : ((23265190694169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT228 (i+1))
      = (∑ i ∈ Finset.range 236, stT228 (i+1)) + stT228 237 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 236
    simpa using h
  have hprev := st228_p236
  have hstep := st228_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p238 : ((22780911003729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT228 (i+1))
      = (∑ i ∈ Finset.range 237, stT228 (i+1)) + stT228 238 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 237
    simpa using h
  have hprev := st228_p237
  have hstep := st228_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p239 : ((22853401094411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT228 (i+1))
      = (∑ i ∈ Finset.range 238, stT228 (i+1)) + stT228 239 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 238
    simpa using h
  have hprev := st228_p238
  have hstep := st228_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p240 : ((2927229653331/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT228 (i+1))
      = (∑ i ∈ Finset.range 239, stT228 (i+1)) + stT228 240 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 239
    simpa using h
  have hprev := st228_p239
  have hstep := st228_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p241 : ((6000043554871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT228 (i+1))
      = (∑ i ∈ Finset.range 240, stT228 (i+1)) + stT228 241 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 240
    simpa using h
  have hprev := st228_p240
  have hstep := st228_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p242 : ((6029616190873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT228 (i+1))
      = (∑ i ∈ Finset.range 241, stT228 (i+1)) + stT228 242 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 241
    simpa using h
  have hprev := st228_p241
  have hstep := st228_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p243 : ((11839390630547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT228 (i+1))
      = (∑ i ∈ Finset.range 242, stT228 (i+1)) + stT228 243 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 242
    simpa using h
  have hprev := st228_p242
  have hstep := st228_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p244 : ((2880402139553/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT228 (i+1))
      = (∑ i ∈ Finset.range 243, stT228 (i+1)) + stT228 244 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 243
    simpa using h
  have hprev := st228_p243
  have hstep := st228_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p245 : ((1136352100007/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT228 (i+1))
      = (∑ i ∈ Finset.range 244, stT228 (i+1)) + stT228 245 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 244
    simpa using h
  have hprev := st228_p244
  have hstep := st228_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p246 : ((5745444938189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT228 (i+1))
      = (∑ i ∈ Finset.range 245, stT228 (i+1)) + stT228 246 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 245
    simpa using h
  have hprev := st228_p245
  have hstep := st228_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p247 : ((737518023737/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT228 (i+1))
      = (∑ i ∈ Finset.range 246, stT228 (i+1)) + stT228 247 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 246
    simpa using h
  have hprev := st228_p246
  have hstep := st228_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p248 : ((3011465403073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT228 (i+1))
      = (∑ i ∈ Finset.range 247, stT228 (i+1)) + stT228 248 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 247
    simpa using h
  have hprev := st228_p247
  have hstep := st228_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p249 : ((24070696862809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT228 (i+1))
      = (∑ i ∈ Finset.range 248, stT228 (i+1)) + stT228 249 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 248
    simpa using h
  have hprev := st228_p248
  have hstep := st228_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_p250 : ((23557328532873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT228 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT228 (i+1))
      = (∑ i ∈ Finset.range 249, stT228 (i+1)) + stT228 250 := by
    have h := Finset.sum_range_succ (fun i => stT228 (i+1)) 249
    simpa using h
  have hprev := st228_p249
  have hstep := st228_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st228_s250 :
    |Real.sin (((228 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))
      - ((73017/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1258889/2000000) (δ := 5783/500000000) (ψ := -261743/1000000) 228 200
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 228`** (evaluated boundary). -/
theorem station_228_sign : 0 < hardyG ((((228:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 228 250 (by norm_num) (by norm_num)
    ((-261743/1000000 : ℚ) : ℝ)
  have hchain := st228_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT228 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((228 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-261743/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st228_c250
  have hsinb := abs_le.mp st228_s250
  have hbdy_lo : ((-2099573749097/51984250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((228 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ))) / 2
          - ((((228:ℕ)):ℝ))
            * Real.sin (((228 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-261743/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((228:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((228:ℝ) * Real.log (250:ℝ) - ((-261743/1000000 : ℚ) : ℝ))) / 2
        - ((228:ℝ)) * Real.sin ((228:ℝ) * Real.log (250:ℝ) - ((-261743/1000000 : ℚ) : ℝ))
        ≥ ((-26557721/200000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((228:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-26557721/200000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-26557721/200000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-26557721/200000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((228:ℕ)):ℝ))+1) * (((((228:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((215375064157/187500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((23557328532873/10000000000000 : ℚ) : ℝ) + ((-2099573749097/51984250000000 : ℚ) : ℝ)
      - ((215375064157/187500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-261743/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((228:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-261743/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((228:ℕ)):ℝ)))).re
      - Real.sin ((-261743/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((228:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((228:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((228:ℕ)):ℝ))
      = (((((228:ℕ)):ℝ)) * (Real.log ((((228:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((228:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_228
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
  have hθwin : |(((-261743/1000000 : ℚ) : ℝ) + ((47:ℤ)) * (2*Real.pi)) - theta ((((228:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((228:ℕ)):ℝ)))
    (φ := ((-261743/1000000 : ℚ) : ℝ) + ((47:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-261743/1000000 : ℚ)) : ℝ) 47).1,
    (cos_sin_shift (((-261743/1000000 : ℚ)) : ℝ) 47).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_228_sign
end AxiomAudit
