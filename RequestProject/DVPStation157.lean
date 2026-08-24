import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 157` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT157 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((157 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((9749/10000 : ℚ) : ℝ))

theorem st157_c1 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((561251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9749/40000) (δ := 1/1000000000) (ψ := 9749/10000) 157 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t1 : ((561201/1000000 : ℚ) : ℝ) ≤ stT157 1 := by
  have hc : ((561201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((561201/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((561201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c2 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((510481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2587631/10000000) (δ := 1981/250000000) (ψ := 9749/10000) 157 17
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t2 : ((3609291799877/10000000000000 : ℚ) : ℝ) ≤ stT157 2 := by
  have hc : ((510431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3609291799877/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((510431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c3 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-143179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93061/200000) (δ := 1579/200000000) (ψ := 9749/10000) 157 27
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t3 : ((-206697180903/1250000000000 : ℚ) : ℝ) ≤ stT157 3 := by
  have hc : ((-35801/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206697180903/1250000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-35801/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c4 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-49767/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7612531/10000000) (δ := 7957/1000000000) (ψ := 9749/10000) 157 34
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t4 : ((-497695099539/1000000000000 : ℚ) : ℝ) ≤ stT157 4 := by
  have hc : ((-99539/100000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497695099539/1000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-99539/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c5 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((92887/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189723/2000000) (δ := 7989/1000000000) (ψ := 9749/10000) 157 40
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t5 : ((41538084307/100000000000 : ℚ) : ℝ) ≤ stT157 5 := by
  have hc : ((46441/50000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41538084307/100000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((46441/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c6 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-745449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6030013/10000000) (δ := 3939/500000000) (ψ := 9749/10000) 157 45
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t6 : ((-3043486994017/10000000000000 : ℚ) : ℝ) ≤ stT157 6 := by
  have hc : ((-745499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3043486994017/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-745499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c7 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-979769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7350247/10000000) (δ := 7857/1000000000) (ψ := 9749/10000) 157 48
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t7 : ((-740673596851/2000000000000 : ℚ) : ℝ) ≤ stT157 7 := by
  have hc : ((-979819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-740673596851/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-979819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c8 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((167961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -767633/2500000) (δ := 2007/250000000) (ψ := 9749/10000) 157 52
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t8 : ((144956853/1220703125 : ℚ) : ℝ) ≤ stT157 8 := by
  have hc : ((5248/15625 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144956853/1220703125 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((5248/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c9 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-15041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1982297/5000000) (δ := 7907/1000000000) (ψ := 9749/10000) 157 55
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t9 : ((-25151671697/5000000000000 : ℚ) : ℝ) ≤ stT157 9 := by
  have hc : ((-15091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25151671697/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-15091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c10 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-365093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493369/2500000) (δ := 7911/1000000000) (ψ := 9749/10000) 157 57
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t10 : ((-288651154701/1250000000000 : ℚ) : ℝ) ≤ stT157 10 := by
  have hc : ((-182559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288651154701/1250000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-182559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c11 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((9283/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -93529/250000) (δ := 251/31250000) (ψ := 9749/10000) 157 60
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t11 : ((111881798091/5000000000000 : ℚ) : ℝ) ≤ stT157 11 := by
  have hc : ((37107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111881798091/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((37107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c12 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((920263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125639/1250000) (δ := 8047/1000000000) (ψ := 9749/10000) 157 62
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t12 : ((2656425797963/10000000000000 : ℚ) : ℝ) ≤ stT157 12 := by
  have hc : ((920213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2656425797963/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((920213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c13 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((920393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1004279/10000000) (δ := 7961/1000000000) (ψ := 9749/10000) 157 64
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t13 : ((5105142621/20000000000 : ℚ) : ℝ) ≤ stT157 13 := by
  have hc : ((920343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5105142621/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((920343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c14 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((235439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -208301/625000) (δ := 991/125000000) (ψ := 9749/10000) 157 66
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t14 : ((157275866517/2500000000000 : ℚ) : ℝ) ≤ stT157 14 := by
  have hc : ((235389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157275866517/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((235389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c15 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-199453/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7669029/10000000) (δ := 789/100000000) (ψ := 9749/10000) 157 68
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t15 : ((-515011271907/2000000000000 : ℚ) : ℝ) ≤ stT157 15 := by
  have hc : ((-199463/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515011271907/2000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-199463/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c16 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((709683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1954369/10000000) (δ := 7897/1000000000) (ψ := 9749/10000) 157 69
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t16 : ((709633/4000000 : ℚ) : ℝ) ≤ stT157 16 := by
  have hc : ((709633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((709633/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((709633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c17 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-160243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2833201/5000000) (δ := 7911/1000000000) (ψ := 9749/10000) 157 71
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t17 : ((-777353597427/5000000000000 : ℚ) : ℝ) ≤ stT157 17 := by
  have hc : ((-320511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-777353597427/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-320511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c18 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((4557/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1060307/10000000) (δ := 4009/500000000) (ψ := 9749/10000) 157 72
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t18 : ((21480719997/100000000000 : ℚ) : ℝ) ≤ stT157 18 := by
  have hc : ((18227/20000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21480719997/100000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((18227/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c19 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-174343/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6573719/10000000) (δ := 7977/1000000000) (ψ := 9749/10000) 157 73
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t19 : ((-199996664887/1000000000000 : ℚ) : ℝ) ≤ stT157 19 := by
  have hc : ((-174353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199996664887/1000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-174353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c20 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-307951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4709587/10000000) (δ := 7863/1000000000) (ψ := 9749/10000) 157 75
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t20 : ((-172177795017/2500000000000 : ℚ) : ℝ) ≤ stT157 20 := by
  have hc : ((-308001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172177795017/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-308001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c21 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((34969/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1267397/10000000) (δ := 1989/250000000) (ψ := 9749/10000) 157 76
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t21 : ((38152109063/200000000000 : ℚ) : ℝ) ≤ stT157 21 := by
  have hc : ((34967/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38152109063/200000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((34967/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c22 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((871033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64187/500000) (δ := 3927/500000000) (ψ := 9749/10000) 157 77
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t22 : ((1856941852881/10000000000000 : ℚ) : ℝ) ≤ stT157 22 := by
  have hc : ((870983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1856941852881/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((870983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c23 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((353727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 755777/2500000) (δ := 7941/1000000000) (ψ := 9749/10000) 157 78
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t23 : ((92183434311/1250000000000 : ℚ) : ℝ) ≤ stT157 23 := by
  have hc : ((353677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92183434311/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((353677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c24 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-3711/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1004947/2500000) (δ := 7869/1000000000) (ψ := 9749/10000) 157 79
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t24 : ((-948156909/125000000000 : ℚ) : ℝ) ≤ stT157 24 := by
  have hc : ((-929/25000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-948156909/125000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-929/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c25 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-162267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 216723/500000) (δ := 997/125000000) (ψ := 9749/10000) 157 80
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t25 : ((-324634162317/10000000000000 : ℚ) : ℝ) ≤ stT157 25 := by
  have hc : ((-162317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324634162317/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-162317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c26 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-37443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4020621/10000000) (δ := 99/12500000) (ψ := 9749/10000) 157 81
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t26 : ((-36764923433/5000000000000 : ℚ) : ℝ) ≤ stT157 26 := by
  have hc : ((-37493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36764923433/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-37493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c27 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((315047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1562863/5000000) (δ := 799/100000000) (ψ := 9749/10000) 157 82
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t27 : ((1212423453/20000000000 : ℚ) : ℝ) ≤ stT157 27 := by
  have hc : ((314997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1212423453/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((314997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c28 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((19489/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 338417/2000000) (δ := 7997/1000000000) (ψ := 9749/10000) 157 83
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t28 : ((73656757361/500000000000 : ℚ) : ℝ) ≤ stT157 28 := by
  have hc : ((77951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73656757361/500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((77951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c29 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((497649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242543/10000000) (δ := 1601/200000000) (ψ := 9749/10000) 157 84
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t29 : ((115508047459/625000000000 : ℚ) : ℝ) ≤ stT157 29 := by
  have hc : ((62203/62500 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115508047459/625000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((62203/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c30 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((245453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330521/1250000) (δ := 7891/1000000000) (ψ := 9749/10000) 157 85
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t30 : ((112021990537/1250000000000 : ℚ) : ℝ) ≤ stT157 30 := by
  have hc : ((61357/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112021990537/1250000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((61357/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c31 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-72837/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1096419/2000000) (δ := 8019/1000000000) (ψ := 9749/10000) 157 86
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t31 : ((-261660821071/2500000000000 : ℚ) : ℝ) ≤ stT157 31 := by
  have hc : ((-291373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261660821071/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-291373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c32 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-234853/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6979269/10000000) (δ := 499/62500000) (ψ := 9749/10000) 157 86
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t32 : ((-830374960677/5000000000000 : ℚ) : ℝ) ≤ stT157 32 := by
  have hc : ((-469731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-830374960677/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-469731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c33 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((5727/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3349159/10000000) (δ := 7877/1000000000) (ψ := 9749/10000) 157 87
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t33 : ((4983624091/125000000000 : ℚ) : ℝ) ≤ stT157 33 := by
  have hc : ((22903/100000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4983624091/125000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((22903/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c34 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((483629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -320751/5000000) (δ := 797/100000000) (ψ := 9749/10000) 157 88
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t34 : ((41468680297/250000000000 : ℚ) : ℝ) ≤ stT157 34 := by
  have hc : ((120901/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41468680297/250000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((120901/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c35 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-40589/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4971871/10000000) (δ := 397/50000000) (ψ := 9749/10000) 157 89
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t35 : ((-34308201773/500000000000 : ℚ) : ℝ) ≤ stT157 35 := by
  have hc : ((-20297/50000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34308201773/500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-20297/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c36 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-759983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6085207/10000000) (δ := 7863/1000000000) (ψ := 9749/10000) 157 89
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t36 : ((-1266721920011/10000000000000 : ℚ) : ℝ) ≤ stT157 36 := by
  have hc : ((-760033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1266721920011/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-760033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c37 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((899339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1131351/10000000) (δ := 1591/200000000) (ψ := 9749/10000) 157 90
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t37 : ((1478421223821/10000000000000 : ℚ) : ℝ) ≤ stT157 37 := by
  have hc : ((899289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1478421223821/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((899289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c38 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-72877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128417/312500) (δ := 503/62500000) (ψ := 9749/10000) 157 91
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t38 : ((-23660654661/2000000000000 : ℚ) : ℝ) ≤ stT157 38 := by
  have hc : ((-72927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23660654661/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-72927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c39 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-760199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152151/250000) (δ := 1987/250000000) (ψ := 9749/10000) 157 91
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t39 : ((-608686519609/5000000000000 : ℚ) : ℝ) ≤ stT157 39 := by
  have hc : ((-760249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-608686519609/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-760249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c40 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((992057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 315313/10000000) (δ := 8041/1000000000) (ψ := 9749/10000) 157 92
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t40 : ((784249981983/5000000000000 : ℚ) : ℝ) ≤ stT157 40 := by
  have hc : ((992007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((784249981983/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((992007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c41 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-325737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1425201/2500000) (δ := 7969/1000000000) (ψ := 9749/10000) 157 93
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t41 : ((-127188723589/1250000000000 : ℚ) : ℝ) ≤ stT157 41 := by
  have hc : ((-162881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127188723589/1250000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-162881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c42 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((67743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58711/156250) (δ := 7969/1000000000) (ψ := 9749/10000) 157 93
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t42 : ((104452532869/10000000000000 : ℚ) : ℝ) ≤ stT157 42 := by
  have hc : ((67693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104452532869/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((67693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c43 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((466121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1357369/5000000) (δ := 997/125000000) (ψ := 9749/10000) 157 94
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t43 : ((142150256787/2000000000000 : ℚ) : ℝ) ≤ stT157 43 := by
  have hc : ((466071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142150256787/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((466071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c44 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-10187/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39429/62500) (δ := 8027/1000000000) (ψ := 9749/10000) 157 94
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t44 : ((-122867403057/1000000000000 : ℚ) : ℝ) ≤ stT157 44 := by
  have hc : ((-81501/100000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122867403057/1000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-81501/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c45 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((973323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -578749/10000000) (δ := 7919/1000000000) (ψ := 9749/10000) 157 95
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t45 : ((1450868767103/10000000000000 : ℚ) : ℝ) ≤ stT157 45 := by
  have hc : ((973273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1450868767103/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((973273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c46 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-996991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3829997/5000000) (δ := 989/125000000) (ψ := 9749/10000) 157 96
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t46 : ((-73502859561/500000000000 : ℚ) : ℝ) ≤ stT157 46 := by
  have hc : ((-997041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73502859561/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-997041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c47 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((951571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 781229/10000000) (δ := 7891/1000000000) (ψ := 9749/10000) 157 96
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t47 : ((1387935155129/10000000000000 : ℚ) : ℝ) ≤ stT157 47 := by
  have hc : ((951521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1387935155129/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((951521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c48 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-177741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266531/400000) (δ := 1581/200000000) (ψ := 9749/10000) 157 97
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t48 : ((-16035095461/125000000000 : ℚ) : ℝ) ≤ stT157 48 := by
  have hc : ((-177751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16035095461/125000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-177751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c49 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((105109/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1429761/10000000) (δ := 1581/200000000) (ψ := 9749/10000) 157 97
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t49 : ((600586962681/5000000000000 : ℚ) : ℝ) ≤ stT157 49 := by
  have hc : ((420411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((600586962681/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((420411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c50 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-824119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6348603/10000000) (δ := 1581/200000000) (ψ := 9749/10000) 157 98
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t50 : ((-582775669083/5000000000000 : ℚ) : ℝ) ≤ stT157 50 := by
  have hc : ((-824169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-582775669083/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-824169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c51 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((168427/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1423917/10000000) (δ := 3999/500000000) (ψ := 9749/10000) 157 98
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t51 : ((5895773919/50000000000 : ℚ) : ℝ) ≤ stT157 51 := by
  have hc : ((168417/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5895773919/50000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((168417/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c52 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-888553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3331221/5000000) (δ := 7991/1000000000) (ψ := 9749/10000) 157 99
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t52 : ((-1232271098853/10000000000000 : ℚ) : ℝ) ≤ stT157 52 := by
  have hc : ((-888603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1232271098853/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-888603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c53 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((473731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 813977/10000000) (δ := 989/125000000) (ψ := 9749/10000) 157 99
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t53 : ((65068493013/500000000000 : ℚ) : ℝ) ≤ stT157 53 := by
  have hc : ((236853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65068493013/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((236853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c54 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-124121/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7557337/10000000) (δ := 7919/1000000000) (ψ := 9749/10000) 157 100
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t54 : ((-168915837363/1250000000000 : ℚ) : ℝ) ≤ stT157 54 := by
  have hc : ((-496509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168915837363/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-496509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c55 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((989917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71063/2000000) (δ := 8019/1000000000) (ψ := 9749/10000) 157 100
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t55 : ((1334735672933/10000000000000 : ℚ) : ℝ) ≤ stT157 55 := by
  have hc : ((989867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1334735672933/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((989867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c56 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-898343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3358473/5000000) (δ := 7919/1000000000) (ψ := 9749/10000) 157 100
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t56 : ((-1200528854651/10000000000000 : ℚ) : ℝ) ≤ stT157 56 := by
  have hc : ((-898393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1200528854651/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-898393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c57 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((170999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -510981/2500000) (δ := 8027/1000000000) (ψ := 9749/10000) 157 101
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t57 : ((113238545409/1250000000000 : ℚ) : ℝ) ≤ stT157 57 := by
  have hc : ((341973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113238545409/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((341973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c58 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-33551/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4782357/10000000) (δ := 1969/250000000) (ψ := 9749/10000) 157 101
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t58 : ((-2203060457/50000000000 : ℚ) : ℝ) ≤ stT157 58 := by
  have hc : ((-8389/25000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2203060457/50000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-8389/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c59 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-14421/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108027/5000000) (δ := 3967/500000000) (ψ := 9749/10000) 157 102
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t59 : ((-7513077001/500000000000 : ℚ) : ℝ) ≤ stT157 59 := by
  have hc : ((-57709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7513077001/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-57709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c60 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((72477/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2380733/10000000) (δ := 4017/500000000) (ψ := 9749/10000) 157 102
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t60 : ((187118606851/2500000000000 : ℚ) : ℝ) ≤ stT157 60 := by
  have hc : ((289883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187118606851/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((289883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c61 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-918787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170987/250000) (δ := 8041/1000000000) (ψ := 9749/10000) 157 103
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t61 : ((-1176450410853/10000000000000 : ℚ) : ℝ) ≤ stT157 61 := by
  have hc : ((-918837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1176450410853/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-918837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c62 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((491661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228617/5000000) (δ := 7941/1000000000) (ψ := 9749/10000) 157 103
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t62 : ((156094552909/1250000000000 : ℚ) : ℝ) ≤ stT157 62 := by
  have hc : ((122909/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156094552909/1250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((122909/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c63 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-687741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5822923/10000000) (δ := 7941/1000000000) (ψ := 9749/10000) 157 103
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t63 : ((-433267750331/5000000000000 : ℚ) : ℝ) ≤ stT157 63 := by
  have hc : ((-687791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433267750331/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-687791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c64 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((17829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3703833/10000000) (δ := 1591/200000000) (ψ := 9749/10000) 157 104
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t64 : ((17819/1600000 : ℚ) : ℝ) ≤ stT157 64 := by
  have hc : ((17819/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17819/1600000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((17819/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c65 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((115909/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1190783/5000000) (δ := 1987/250000000) (ψ := 9749/10000) 157 104
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t65 : ((143754976953/2000000000000 : ℚ) : ℝ) ≤ stT157 65 := by
  have hc : ((115899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143754976953/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((115899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c66 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-978439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -458369/625000) (δ := 1987/250000000) (ψ := 9749/10000) 157 105
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t66 : ((-240887357487/2000000000000 : ℚ) : ℝ) ≤ stT157 66 := by
  have hc : ((-978489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240887357487/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-978489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c67 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((840489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -178941/1250000) (δ := 1571/200000000) (ψ := 9749/10000) 157 105
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t67 : ((513379641833/5000000000000 : ℚ) : ℝ) ≤ stT157 67 := by
  have hc : ((840439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((513379641833/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((840439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c68 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-181551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4383399/10000000) (δ := 1591/200000000) (ψ := 9749/10000) 157 105
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t68 : ((-220223719079/10000000000000 : ℚ) : ℝ) ≤ stT157 68 := by
  have hc : ((-181601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220223719079/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-181601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c69 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-309323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -699317/1250000) (δ := 201/25000000) (ψ := 9749/10000) 157 106
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t69 : ((-93102843483/1250000000000 : ℚ) : ℝ) ≤ stT157 69 := by
  have hc : ((-77337/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93102843483/1250000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-77337/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c70 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((39991/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53029/10000000) (δ := 397/50000000) (ψ := 9749/10000) 157 106
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t70 : ((11948993123/100000000000 : ℚ) : ℝ) ≤ stT157 70 := by
  have hc : ((39989/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11948993123/100000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((39989/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c71 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-626767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1124097/2000000) (δ := 7963/1000000000) (ψ := 9749/10000) 157 106
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t71 : ((-371947566447/5000000000000 : ℚ) : ℝ) ≤ stT157 71 := by
  have hc : ((-626817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371947566447/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-626817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c72 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-265137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143683/312500) (δ := 7933/1000000000) (ψ := 9749/10000) 157 107
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t72 : ((-19532878859/625000000000 : ℚ) : ℝ) ≤ stT157 72 := by
  have hc : ((-265187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19532878859/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-265187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c73 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((947201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 408007/5000000) (δ := 8033/1000000000) (ψ := 9749/10000) 157 107
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t73 : ((1108555949061/10000000000000 : ℚ) : ℝ) ≤ stT157 73 := by
  have hc : ((947151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1108555949061/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((947151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c74 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-778133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1539053/2500000) (δ := 8033/1000000000) (ψ := 9749/10000) 157 107
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t74 : ((-904619839291/10000000000000 : ℚ) : ℝ) ≤ stT157 74 := by
  have hc : ((-778183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-904619839291/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-778183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c75 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-35499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267699/625000) (δ := 7877/1000000000) (ψ := 9749/10000) 157 108
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t75 : ((-82010329123/5000000000000 : ℚ) : ℝ) ≤ stT157 75 := by
  have hc : ((-71023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82010329123/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-71023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c76 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((933687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 915557/10000000) (δ := 7877/1000000000) (ψ := 9749/10000) 157 108
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t76 : ((535477231343/5000000000000 : ℚ) : ℝ) ≤ stT157 76 := by
  have hc : ((933637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((535477231343/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((933637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c77 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-749791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1511589/2500000) (δ := 3963/500000000) (ψ := 9749/10000) 157 108
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t77 : ((-427261651323/5000000000000 : ℚ) : ℝ) ≤ stT157 77 := by
  have hc : ((-749841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427261651323/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-749841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c78 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-16551/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4597023/10000000) (δ := 8019/1000000000) (ψ := 9749/10000) 157 109
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t78 : ((-74975486187/2500000000000 : ℚ) : ℝ) ≤ stT157 78 := by
  have hc : ((-132433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74975486187/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-132433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c79 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((987033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80607/2000000) (δ := 1971/250000000) (ψ := 9749/10000) 157 109
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t79 : ((1110441742521/10000000000000 : ℚ) : ℝ) ≤ stT157 79 := by
  have hc : ((986983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1110441742521/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((986983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c80 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-26783/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2670107/5000000) (δ := 1971/250000000) (ψ := 9749/10000) 157 109
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t80 : ((-29947099707/500000000000 : ℚ) : ℝ) ≤ stT157 80 := by
  have hc : ((-53571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29947099707/500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-53571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c81 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-146471/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2745959/5000000) (δ := 7891/1000000000) (ψ := 9749/10000) 157 110
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t81 : ((-40689893663/625000000000 : ℚ) : ℝ) ≤ stT157 81 := by
  have hc : ((-292967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40689893663/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-292967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c82 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((481837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10561/156250) (δ := 989/125000000) (ψ := 9749/10000) 157 110
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t82 : ((26603610939/250000000000 : ℚ) : ℝ) ≤ stT157 82 := by
  have hc : ((120453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26603610939/250000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((120453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c83 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-61863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2040873/5000000) (δ := 7991/1000000000) (ψ := 9749/10000) 157 110
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t83 : ((-67958371059/10000000000000 : ℚ) : ℝ) ≤ stT157 83 := by
  have hc : ((-61913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67958371059/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-61913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c84 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-465917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6925579/10000000) (δ := 3161/200000000) (ψ := 9749/10000) 157 111
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t84 : ((-25419232839/250000000000 : ℚ) : ℝ) ≤ stT157 84 := by
  have hc : ((-232971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25419232839/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-232971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c85 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((611989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2280557/10000000) (δ := 3949/500000000) (ψ := 9749/10000) 157 111
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t85 : ((165935215057/2500000000000 : ℚ) : ℝ) ≤ stT157 85 := by
  have hc : ((611939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165935215057/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((611939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c86 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((301297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2310123/10000000) (δ := 3949/500000000) (ψ := 9749/10000) 157 111
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t86 : ((40608716493/625000000000 : ℚ) : ℝ) ≤ stT157 86 := by
  have hc : ((37659/62500 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40608716493/625000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((37659/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c87 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-230023/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213993/312500) (δ := 1581/200000000) (ψ := 9749/10000) 157 111
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t87 : ((-493248100023/5000000000000 : ℚ) : ℝ) ≤ stT157 87 := by
  have hc : ((-460071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-493248100023/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-460071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c88 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-178019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2187211/5000000) (δ := 4003/500000000) (ψ := 9749/10000) 157 112
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t88 : ((-47455566569/2500000000000 : ℚ) : ℝ) ≤ stT157 88 := by
  have hc : ((-178069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47455566569/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-178069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c89 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((499853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60631/10000000) (δ := 7997/1000000000) (ψ := 9749/10000) 157 112
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t89 : ((132454045129/1250000000000 : ℚ) : ℝ) ≤ stT157 89 := by
  have hc : ((124957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132454045129/1250000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((124957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c90 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-8247/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 555769/1250000) (δ := 4003/500000000) (ψ := 9749/10000) 157 112
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t90 : ((-8695213157/400000000000 : ℚ) : ℝ) ≤ stT157 90 := by
  have hc : ((-8249/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8695213157/400000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-8249/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c91 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-931713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3462373/5000000) (δ := 1589/100000000) (ψ := 9749/10000) 157 113
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t91 : ((-195350635291/2000000000000 : ℚ) : ℝ) ≤ stT157 91 := by
  have hc : ((-931763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195350635291/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-931763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c92 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((98813/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2635093/10000000) (δ := 8013/1000000000) (ψ := 9749/10000) 157 113
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t92 : ((25752310329/500000000000 : ℚ) : ℝ) ≤ stT157 92 := by
  have hc : ((98803/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25752310329/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((98803/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c93 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((100017/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321637/2000000) (δ := 7913/1000000000) (ψ := 9749/10000) 157 113
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t93 : ((414824988893/5000000000000 : ℚ) : ℝ) ≤ stT157 93 := by
  have hc : ((400043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414824988893/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((400043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c94 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-341419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 580609/1000000) (δ := 789/100000000) (ψ := 9749/10000) 157 113
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t94 : ((-44021606671/625000000000 : ℚ) : ℝ) ≤ stT157 94 := by
  have hc : ((-85361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44021606671/625000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-85361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c95 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-332899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5748399/10000000) (δ := 7883/1000000000) (ψ := 9749/10000) 157 114
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t95 : ((-85393258149/1250000000000 : ℚ) : ℝ) ≤ stT157 95 := by
  have hc : ((-83231/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85393258149/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-83231/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c96 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((31713/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -819207/5000000) (δ := 7983/1000000000) (ψ := 9749/10000) 157 114
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t96 : ((1618244041/20000000000 : ℚ) : ℝ) ≤ stT157 96 := by
  have hc : ((31711/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1618244041/20000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((31711/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c97 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((35249/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 485797/2000000) (δ := 7983/1000000000) (ψ := 9749/10000) 157 114
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t97 : ((143147032791/2500000000000 : ℚ) : ℝ) ≤ stT157 97 := by
  have hc : ((281967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143147032791/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((281967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c98 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-4237/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3227331/5000000) (δ := 401/50000000) (ψ := 9749/10000) 157 114
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t98 : ((-17121083197/200000000000 : ℚ) : ℝ) ≤ stT157 98 := by
  have hc : ((-16949/20000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17121083197/200000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-16949/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c99 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-102243/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053697/2000000) (δ := 997/125000000) (ψ := 9749/10000) 157 115
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t99 : ((-51384075307/1000000000000 : ℚ) : ℝ) ≤ stT157 99 := by
  have hc : ((-102253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51384075307/1000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-102253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c100 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((863061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -661871/5000000) (δ := 1969/250000000) (ψ := 9749/10000) 157 115
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t100 : ((863010136989/10000000000000 : ℚ) : ℝ) ≤ stT157 100 := by
  have hc : ((863011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((863010136989/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((863011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c101 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((512489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258179/1000000) (δ := 1969/250000000) (ψ := 9749/10000) 157 115
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t101 : ((509895765243/10000000000000 : ℚ) : ℝ) ≤ stT157 101 := by
  have hc : ((512439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((509895765243/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((512439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c102 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-211539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3224409/5000000) (δ := 7927/1000000000) (ψ := 9749/10000) 157 115
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t102 : ((-104733647311/1250000000000 : ℚ) : ℝ) ≤ stT157 102 := by
  have hc : ((-423103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104733647311/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-423103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c103 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-113119/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1357469/2500000) (δ := 3967/500000000) (ψ := 9749/10000) 157 116
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t103 : ((-11146939757/200000000000 : ℚ) : ℝ) ≤ stT157 103 := by
  have hc : ((-113129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11146939757/200000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-113129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c104 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((198257/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81879/500000) (δ := 4017/500000000) (ψ := 9749/10000) 157 116
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t104 : ((19439459181/250000000000 : ℚ) : ℝ) ≤ stT157 104 := by
  have hc : ((396489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19439459181/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((396489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c105 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((13239/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132403/625000) (δ := 7969/1000000000) (ψ := 9749/10000) 157 116
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t105 : ((64594821/1000000000 : ℚ) : ℝ) ≤ stT157 105 := by
  have hc : ((6619/10000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64594821/1000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((6619/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c106 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-692349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2919419/5000000) (δ := 7869/1000000000) (ψ := 9749/10000) 157 116
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t106 : ((-336258727557/5000000000000 : ℚ) : ℝ) ≤ stT157 106 := by
  have hc : ((-692399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336258727557/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-692399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c107 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-31399/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6183629/10000000) (δ := 7961/1000000000) (ψ := 9749/10000) 157 117
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t107 : ((-30356508537/400000000000 : ℚ) : ℝ) ≤ stT157 107 := by
  have hc : ((-31401/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30356508537/400000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-31401/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c108 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((529339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2532437/10000000) (δ := 7961/1000000000) (ψ := 9749/10000) 157 117
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t108 : ((2037233361/40000000000 : ℚ) : ℝ) ≤ stT157 108 := by
  have hc : ((529289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2037233361/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((529289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c109 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((453639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1085079/10000000) (δ := 3971/500000000) (ψ := 9749/10000) 157 117
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t109 : ((108620820791/1250000000000 : ℚ) : ℝ) ≤ stT157 109 := by
  have hc : ((226807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108620820791/1250000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((226807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c110 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-292689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 933917/2000000) (δ := 7861/1000000000) (ψ := 9749/10000) 157 117
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t110 : ((-279115805157/10000000000000 : ℚ) : ℝ) ≤ stT157 110 := by
  have hc : ((-292739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279115805157/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-292739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c111 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-247301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1871573/2500000) (δ := 8049/1000000000) (ψ := 9749/10000) 157 118
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t111 : ((-234739587033/2500000000000 : ℚ) : ℝ) ≤ stT157 111 := by
  have hc : ((-494627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234739587033/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-494627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c112 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-313/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3966117/10000000) (δ := 3927/500000000) (ψ := 9749/10000) 157 118
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t112 : ((-9271949/6250000000 : ℚ) : ℝ) ≤ stT157 112 := by
  have hc : ((-157/10000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9271949/6250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-157/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c113 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((981839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3728/78125) (δ := 8049/1000000000) (ψ := 9749/10000) 157 118
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t113 : ((11544856851/125000000000 : ℚ) : ℝ) ≤ stT157 113 := by
  have hc : ((981789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11544856851/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((981789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c114 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((2309/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186311/625000) (δ := 3927/500000000) (ψ := 9749/10000) 157 118
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t114 : ((6919302663/200000000000 : ℚ) : ℝ) ≤ stT157 114 := by
  have hc : ((36939/100000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6919302663/200000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((36939/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c115 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-837551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6408953/10000000) (δ := 3977/500000000) (ψ := 9749/10000) 157 118
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t115 : ((-156213424101/2000000000000 : ℚ) : ℝ) ≤ stT157 115 := by
  have hc : ((-837601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156213424101/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-837601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c116 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-355001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1180149/2000000) (δ := 491/62500000) (ψ := 9749/10000) 157 119
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t116 : ((-164816737701/2500000000000 : ℚ) : ℝ) ≤ stT157 116 := by
  have hc : ((-177513/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164816737701/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-177513/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c117 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((264811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -632901/2500000) (δ := 8047/1000000000) (ψ := 9749/10000) 157 119
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t117 : ((244794657/5000000000 : ℚ) : ℝ) ≤ stT157 117 := by
  have hc : ((132393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244794657/5000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((132393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c118 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((237029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404423/5000000) (δ := 7947/1000000000) (ψ := 9749/10000) 157 119
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t118 : ((218191227471/2500000000000 : ℚ) : ℝ) ≤ stT157 118 := by
  have hc : ((474033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218191227471/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((474033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c119 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-19389/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164843/400000) (δ := 7947/1000000000) (ψ := 9749/10000) 157 119
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t119 : ((-35570671297/5000000000000 : ℚ) : ℝ) ≤ stT157 119 := by
  have hc : ((-38803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35570671297/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-38803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c120 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-491981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7405633/10000000) (δ := 491/62500000) (ψ := 9749/10000) 157 119
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t120 : ((-224569004613/2500000000000 : ℚ) : ℝ) ≤ stT157 120 := by
  have hc : ((-246003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224569004613/2500000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-246003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c121 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-27029/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5045051/10000000) (δ := 7963/1000000000) (ψ := 9749/10000) 157 120
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t121 : ((-196597292387/5000000000000 : ℚ) : ℝ) ≤ stT157 121 := by
  have hc : ((-216257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196597292387/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-216257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c122 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((747947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90729/500000) (δ := 7863/1000000000) (ψ := 9749/10000) 157 120
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t122 : ((677113784229/10000000000000 : ℚ) : ℝ) ≤ stT157 122 := by
  have hc : ((747897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677113784229/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((747897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c123 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((33979/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 277903/2000000) (δ := 397/50000000) (ψ := 9749/10000) 157 120
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t123 : ((30636007613/400000000000 : ℚ) : ℝ) ≤ stT157 123 := by
  have hc : ((33977/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30636007613/400000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((33977/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c124 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-126737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2283833/5000000) (δ := 397/50000000) (ψ := 9749/10000) 157 120
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t124 : ((-56917849287/2500000000000 : ℚ) : ℝ) ≤ stT157 124 := by
  have hc : ((-63381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56917849287/2500000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-63381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c125 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-998571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1544061/2000000) (δ := 7963/1000000000) (ψ := 9749/10000) 157 120
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t125 : ((-223298645947/2500000000000 : ℚ) : ℝ) ≤ stT157 125 := by
  have hc : ((-998621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223298645947/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-998621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c126 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-364653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243007/500000) (δ := 787/100000000) (ψ := 9749/10000) 157 121
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t126 : ((-324903326313/10000000000000 : ℚ) : ℝ) ≤ stT157 126 := by
  have hc : ((-364703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324903326313/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-364703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c127 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((152587/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -439347/2500000) (δ := 797/100000000) (ψ := 9749/10000) 157 121
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t127 : ((33847529103/500000000000 : ℚ) : ℝ) ≤ stT157 127 := by
  have hc : ((152577/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33847529103/500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((152577/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c128 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((863601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330267/2500000) (δ := 797/100000000) (ψ := 9749/10000) 157 121
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t128 : ((763278048533/10000000000000 : ℚ) : ℝ) ≤ stT157 128 := by
  have hc : ((863551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((763278048533/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((863551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c129 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-7139/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4375581/10000000) (δ := 7933/1000000000) (ψ := 9749/10000) 157 121
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t129 : ((-6287300591/400000000000 : ℚ) : ℝ) ≤ stT157 129 := by
  have hc : ((-7141/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6287300591/400000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-7141/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c130 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-984021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3703233/5000000) (δ := 7933/1000000000) (ψ := 9749/10000) 157 121
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t130 : ((-863088327189/10000000000000 : ℚ) : ℝ) ≤ stT157 130 := by
  have hc : ((-984071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-863088327189/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-984071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c131 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-259947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5293809/10000000) (δ := 3963/500000000) (ψ := 9749/10000) 157 122
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t131 : ((-11356941813/250000000000 : ℚ) : ℝ) ≤ stT157 131 := by
  have hc : ((-64993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11356941813/250000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-64993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c132 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((602951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2309003/10000000) (δ := 7977/1000000000) (ψ := 9749/10000) 157 122
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t132 : ((131189448897/2500000000000 : ℚ) : ℝ) ≤ stT157 132 := by
  have hc : ((602901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131189448897/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((602901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c133 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((966053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653273/10000000) (δ := 7977/1000000000) (ψ := 9749/10000) 157 122
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t133 : ((837629895327/10000000000000 : ℚ) : ℝ) ≤ stT157 133 := by
  have hc : ((966003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((837629895327/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((966003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c134 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((133059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3593353/10000000) (δ := 15777/1000000000) (ψ := 9749/10000) 157 122
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t134 : ((28725554703/2500000000000 : ℚ) : ℝ) ≤ stT157 134 := by
  have hc : ((133009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28725554703/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((133009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c135 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-429633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6511571/10000000) (δ := 7977/1000000000) (ψ := 9749/10000) 157 122
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t135 : ((-184895371627/2500000000000 : ℚ) : ℝ) ≤ stT157 135 := by
  have hc : ((-214829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184895371627/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-214829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c136 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-812883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6299703/10000000) (δ := 1597/200000000) (ψ := 9749/10000) 157 123
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t136 : ((-697084356969/10000000000000 : ℚ) : ℝ) ≤ stT157 136 := by
  have hc : ((-812933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-697084356969/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-812933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c137 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((2497/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3424209/10000000) (δ := 1577/200000000) (ψ := 9749/10000) 157 123
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t137 : ((17062363647/1000000000000 : ℚ) : ℝ) ≤ stT157 137 := by
  have hc : ((19971/100000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17062363647/1000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((19971/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c138 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((19483/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284837/5000000) (δ := 1597/200000000) (ψ := 9749/10000) 157 123
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t138 : ((1036510587/12500000000 : ℚ) : ℝ) ≤ stT157 138 := by
  have hc : ((9741/10000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1036510587/12500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((9741/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c139 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((617121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2264293/10000000) (δ := 4009/500000000) (ψ := 9749/10000) 157 123
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t139 : ((130848054337/2500000000000 : ℚ) : ℝ) ≤ stT157 139 := by
  have hc : ((617071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130848054337/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((617071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c140 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-88857/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 507793/1000000) (δ := 1597/200000000) (ψ := 9749/10000) 157 123
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t140 : ((-15021277877/400000000000 : ℚ) : ℝ) ≤ stT157 140 := by
  have hc : ((-88867/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15021277877/400000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-88867/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c141 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-39999/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3918227/5000000) (δ := 1973/250000000) (ψ := 9749/10000) 157 124
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t141 : ((-4210865269/50000000000 : ℚ) : ℝ) ≤ stT157 141 := by
  have hc : ((-40001/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4210865269/50000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-40001/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c142 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-17551/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2531289/5000000) (δ := 1973/250000000) (ψ := 9749/10000) 157 124
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t142 : ((-7365080823/200000000000 : ℚ) : ℝ) ≤ stT157 142 := by
  have hc : ((-17553/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7365080823/200000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-17553/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c143 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((603217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -230817/1000000) (δ := 1973/250000000) (ψ := 9749/10000) 157 124
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t143 : ((252196789207/5000000000000 : ℚ) : ℝ) ≤ stT157 143 := by
  have hc : ((603167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252196789207/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((603167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c144 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((985449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85401/2000000) (δ := 8011/1000000000) (ψ := 9749/10000) 157 124
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t144 : ((821165504867/10000000000000 : ℚ) : ℝ) ≤ stT157 144 := by
  have hc : ((985399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((821165504867/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((985399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c145 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((308367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1571651/5000000) (δ := 999/125000000) (ψ := 9749/10000) 157 124
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t145 : ((128021542959/5000000000000 : ℚ) : ℝ) ≤ stT157 145 := by
  have hc : ((308317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128021542959/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((308317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c146 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-173237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1168183/2000000) (δ := 1973/250000000) (ψ := 9749/10000) 157 124
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t146 : ((-143382325697/2500000000000 : ℚ) : ℝ) ≤ stT157 146 := by
  have hc : ((-346499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143382325697/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-346499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c147 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-482357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7187883/10000000) (δ := 2001/250000000) (ψ := 9749/10000) 157 125
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t147 : ((-198931201317/2500000000000 : ℚ) : ℝ) ≤ stT157 147 := by
  have hc : ((-241191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198931201317/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-241191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c148 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-14853/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90537/200000) (δ := 7999/1000000000) (ψ := 9749/10000) 157 125
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t148 : ((-19538656751/1000000000000 : ℚ) : ℝ) ≤ stT157 148 := by
  have hc : ((-118849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19538656751/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-118849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c149 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((182327/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -470929/2500000) (δ := 7899/1000000000) (ψ := 9749/10000) 157 125
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t149 : ((298715380299/5000000000000 : ℚ) : ℝ) ≤ stT157 149 := by
  have hc : ((364629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298715380299/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((364629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c150 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((191263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 741677/10000000) (δ := 247/31250000) (ψ := 9749/10000) 157 125
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t150 : ((9759831843/125000000000 : ℚ) : ℝ) ≤ stT157 150 := by
  have hc : ((191253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9759831843/125000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((191253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c151 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((57219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3349683/10000000) (δ := 7999/1000000000) (ψ := 9749/10000) 157 125
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t151 : ((23276981611/1250000000000 : ℚ) : ℝ) ≤ stT157 151 := by
  have hc : ((114413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23276981611/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((114413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c152 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-360549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5940457/10000000) (δ := 2001/250000000) (ψ := 9749/10000) 157 125
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t152 : ((-36558056999/625000000000 : ℚ) : ℝ) ≤ stT157 152 := by
  have hc : ((-180287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36558056999/625000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-180287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c153 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-965327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3596863/5000000) (δ := 4003/500000000) (ψ := 9749/10000) 157 126
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t153 : ((-780461931781/10000000000000 : ℚ) : ℝ) ≤ stT157 153 := by
  have hc : ((-965377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-780461931781/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-965377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c154 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-280089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4636707/10000000) (δ := 7997/1000000000) (ψ := 9749/10000) 157 126
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t154 : ((-225742449397/10000000000000 : ℚ) : ℝ) ≤ stT157 154 := by
  have hc : ((-280139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225742449397/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-280139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c155 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((668579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1677/8000) (δ := 4003/500000000) (ψ := 9749/10000) 157 126
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t155 : ((536975194851/10000000000000 : ℚ) : ℝ) ≤ stT157 155 := by
  have hc : ((668529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((536975194851/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((668529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c156 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((985389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213939/5000000) (δ := 3953/500000000) (ψ := 9749/10000) 157 126
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t156 : ((1232659089/15625000000 : ℚ) : ℝ) ≤ stT157 156 := by
  have hc : ((985339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1232659089/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((985339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c157 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((386143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1467937/5000000) (δ := 7997/1000000000) (ψ := 9749/10000) 157 126
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t157 : ((154067708999/5000000000000 : ℚ) : ℝ) ≤ stT157 157 := by
  have hc : ((386093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154067708999/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((386093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c158 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-282477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1085587/2000000) (δ := 7997/1000000000) (ψ := 9749/10000) 157 126
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t158 : ((-56186681529/1250000000000 : ℚ) : ℝ) ≤ stT157 158 := by
  have hc : ((-141251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56186681529/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-141251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c159 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-999797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7803667/10000000) (δ := 789/100000000) (ψ := 9749/10000) 157 127
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t159 : ((-198232665761/2500000000000 : ℚ) : ℝ) ≤ stT157 159 := by
  have hc : ((-999847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198232665761/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-999847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c160 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-10731/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5342849/10000000) (δ := 789/100000000) (ψ := 9749/10000) 157 127
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t160 : ((-212109931/5000000000 : ℚ) : ℝ) ≤ stT157 160 := by
  have hc : ((-2683/5000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212109931/5000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-2683/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c161 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((400301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1448689/5000000) (δ := 799/100000000) (ψ := 9749/10000) 157 127
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t161 : ((31544181561/1000000000000 : ℚ) : ℝ) ≤ stT157 161 := by
  have hc : ((400251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31544181561/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((400251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c162 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((491301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233509/5000000) (δ := 799/100000000) (ψ := 9749/10000) 157 127
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t162 : ((48247847503/625000000000 : ℚ) : ℝ) ≤ stT157 162 := by
  have hc : ((122819/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48247847503/625000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((122819/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c163 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((711367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 487097/2500000) (δ := 789/100000000) (ψ := 9749/10000) 157 127
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t163 : ((27857307671/500000000000 : ℚ) : ℝ) ≤ stT157 163 := by
  have hc : ((711317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27857307671/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((711317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c164 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-84001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4348997/10000000) (δ := 8013/1000000000) (ψ := 9749/10000) 157 127
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t164 : ((-32806649297/2500000000000 : ℚ) : ℝ) ≤ stT157 164 := by
  have hc : ((-42013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32806649297/2500000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-42013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c165 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-225373/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1683751/2500000) (δ := 789/100000000) (ψ := 9749/10000) 157 127
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t165 : ((-350924772729/5000000000000 : ℚ) : ℝ) ≤ stT157 165 := by
  have hc : ((-450771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350924772729/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-450771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c166 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-877079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1650339/2500000) (δ := 401/50000000) (ψ := 9749/10000) 157 128
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t166 : ((-680784550479/10000000000000 : ℚ) : ℝ) ≤ stT157 166 := by
  have hc : ((-877129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-680784550479/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-877129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c167 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-126449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2121981/5000000) (δ := 99/12500000) (ψ := 9749/10000) 157 128
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t167 : ((-1529499409/156250000000 : ℚ) : ℝ) ≤ stT157 167 := by
  have hc : ((-126499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1529499409/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-126499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c168 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((181161/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -950349/5000000) (δ := 7883/1000000000) (ψ := 9749/10000) 157 128
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t168 : ((69879483063/1250000000000 : ℚ) : ℝ) ≤ stT157 168 := by
  have hc : ((362297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69879483063/1250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((362297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c169 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((985333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428711/10000000) (δ := 7883/1000000000) (ψ := 9749/10000) 157 128
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t169 : ((75790924209/1000000000000 : ℚ) : ℝ) ≤ stT157 169 := by
  have hc : ((985283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75790924209/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((985283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c170 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((113903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2744343/10000000) (δ := 7983/1000000000) (ψ := 9749/10000) 157 128
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t170 : ((43674956721/1250000000000 : ℚ) : ℝ) ≤ stT157 170 := by
  have hc : ((227781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43674956721/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((227781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c171 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-432949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1009279/2000000) (δ := 7883/1000000000) (ψ := 9749/10000) 157 128
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t171 : ((-4139037441/125000000000 : ℚ) : ℝ) ≤ stT157 171 := by
  have hc : ((-432999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4139037441/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-432999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c172 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-244633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7335023/10000000) (δ := 7983/1000000000) (ψ := 9749/10000) 157 128
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t172 : ((-373080962463/5000000000000 : ℚ) : ℝ) ≤ stT157 172 := by
  have hc : ((-489291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373080962463/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-489291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c173 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-76319/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3048789/5000000) (δ := 991/125000000) (ψ := 9749/10000) 157 129
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t173 : ((-7253508583/125000000000 : ℚ) : ℝ) ≤ stT157 173 := by
  have hc : ((-19081/25000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7253508583/125000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-19081/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c174 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((18329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1917663/5000000) (δ := 63/8000000) (ψ := 9749/10000) 157 129
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t174 : ((54204007/19531250000 : ℚ) : ℝ) ≤ stT157 174 := by
  have hc : ((572/15625 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54204007/19531250000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((572/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c175 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((805421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -793013/5000000) (δ := 991/125000000) (ψ := 9749/10000) 157 129
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t175 : ((76100311161/1250000000000 : ℚ) : ℝ) ≤ stT157 175 := by
  have hc : ((805371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76100311161/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((805371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c176 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((193269/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 650439/10000000) (δ := 991/125000000) (ψ := 9749/10000) 157 129
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t176 : ((72837191251/1000000000000 : ℚ) : ℝ) ≤ stT157 176 := by
  have hc : ((193259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72837191251/1000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((193259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c177 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((102189/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 574853/2000000) (δ := 319/40000000) (ψ := 9749/10000) 157 129
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t177 : ((76800557519/2500000000000 : ℚ) : ℝ) ≤ stT157 177 := by
  have hc : ((204353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76800557519/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((204353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c178 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-447007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1271383/2500000) (δ := 991/125000000) (ψ := 9749/10000) 157 129
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t178 : ((-83770881831/2500000000000 : ℚ) : ℝ) ≤ stT157 178 := by
  have hc : ((-447057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83770881831/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-447057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c179 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-974161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1456887/2000000) (δ := 2007/250000000) (ψ := 9749/10000) 157 129
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t179 : ((-182040093249/2500000000000 : ℚ) : ℝ) ≤ stT157 179 := by
  have hc : ((-974211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182040093249/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-974211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c180 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-797999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6236911/10000000) (δ := 1587/200000000) (ψ := 9749/10000) 157 130
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t180 : ((-148707652611/2500000000000 : ℚ) : ℝ) ≤ stT157 180 := by
  have hc : ((-798049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148707652611/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-798049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c181 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-5413/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4062383/10000000) (δ := 249/31250000) (ψ := 9749/10000) 157 130
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t181 : ((-402717231/100000000000 : ℚ) : ℝ) ≤ stT157 181 := by
  have hc : ((-2709/50000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402717231/100000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-2709/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c182 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((724873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -379973/2000000) (δ := 249/31250000) (ψ := 9749/10000) 157 130
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t182 : ((537274323927/10000000000000 : ℚ) : ℝ) ≤ stT157 182 := by
  have hc : ((724823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537274323927/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((724823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c183 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((994971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250839/10000000) (δ := 1967/250000000) (ψ := 9749/10000) 157 130
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t183 : ((735466496541/10000000000000 : ℚ) : ℝ) ≤ stT157 183 := by
  have hc : ((994921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((735466496541/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((994921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c184 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((115371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2389807/10000000) (δ := 1967/250000000) (ψ := 9749/10000) 157 130
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t184 : ((85045167449/2000000000000 : ℚ) : ℝ) ≤ stT157 184 := by
  have hc : ((115361/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85045167449/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((115361/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c185 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-46779/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1129299/2500000) (δ := 249/31250000) (ψ := 9749/10000) 157 130
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t185 : ((-6879994927/400000000000 : ℚ) : ℝ) ≤ stT157 185 := by
  have hc : ((-46789/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6879994927/400000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-46789/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c186 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-27597/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1326617/2000000) (δ := 249/31250000) (ψ := 9749/10000) 157 130
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t186 : ((-80945038293/1250000000000 : ℚ) : ℝ) ≤ stT157 186 := by
  have hc : ((-441577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80945038293/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-441577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c187 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-37527/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6970293/10000000) (δ := 7861/1000000000) (ψ := 9749/10000) 157 131
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t187 : ((-27443944417/400000000000 : ℚ) : ℝ) ≤ stT157 187 := by
  have hc : ((-37529/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27443944417/400000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-37529/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c188 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-185457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4876973/10000000) (δ := 7961/1000000000) (ψ := 9749/10000) 157 131
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t188 : ((-2705533193/100000000000 : ℚ) : ℝ) ≤ stT157 188 := by
  have hc : ((-92741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2705533193/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-92741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c189 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((218791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2794721/10000000) (δ := 7861/1000000000) (ψ := 9749/10000) 157 131
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t189 : ((2486384973/78125000000 : ℚ) : ℝ) ≤ stT157 189 := by
  have hc : ((109383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2486384973/78125000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((109383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c190 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((59901/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361749/5000000) (δ := 4021/500000000) (ψ := 9749/10000) 157 131
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t190 : ((86908941527/1250000000000 : ℚ) : ℝ) ≤ stT157 190 := by
  have hc : ((479183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86908941527/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((479183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c191 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((860393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1336891/10000000) (δ := 7861/1000000000) (ψ := 9749/10000) 157 131
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t191 : ((311260912941/5000000000000 : ℚ) : ℝ) ≤ stT157 191 := by
  have hc : ((860343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311260912941/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((860343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c192 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((214521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3386487/10000000) (δ := 3971/500000000) (ψ := 9749/10000) 157 131
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t192 : ((154780932577/10000000000000 : ℚ) : ℝ) ≤ stT157 192 := by
  have hc : ((214471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154780932577/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((214471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c193 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-141033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2712723/5000000) (δ := 3971/500000000) (ψ := 9749/10000) 157 131
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t193 : ((-25381701907/625000000000 : ℚ) : ℝ) ≤ stT157 193 := by
  have hc : ((-282091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25381701907/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-282091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c194 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-987221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3726943/5000000) (δ := 3971/500000000) (ψ := 9749/10000) 157 131
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t194 : ((-708820099889/10000000000000 : ℚ) : ℝ) ≤ stT157 194 := by
  have hc : ((-987271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-708820099889/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-987271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c195 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-398899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3118039/5000000) (δ := 3927/500000000) (ψ := 9749/10000) 157 132
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t195 : ((-14283773013/250000000000 : ℚ) : ℝ) ≤ stT157 195 := by
  have hc : ((-99731/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14283773013/250000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-99731/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c196 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-7517/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4228401/10000000) (δ := 7949/1000000000) (ψ := 9749/10000) 157 132
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t196 : ((-21486080023/2500000000000 : ℚ) : ℝ) ≤ stT157 196 := by
  have hc : ((-60161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21486080023/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-60161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c197 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((627567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2230929/10000000) (δ := 8049/1000000000) (ψ := 9749/10000) 157 132
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t197 : ((44708703699/1000000000000 : ℚ) : ℝ) ≤ stT157 197 := by
  have hc : ((627517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44708703699/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((627517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c198 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((995257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1903/78125) (δ := 7949/1000000000) (ψ := 9749/10000) 157 132
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t198 : ((707262763483/10000000000000 : ℚ) : ℝ) ≤ stT157 198 := by
  have hc : ((995207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((707262763483/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((995207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c199 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((769013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 216719/1250000) (δ := 3977/500000000) (ψ := 9749/10000) 157 132
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t199 : ((545103260403/10000000000000 : ℚ) : ℝ) ≤ stT157 199 := by
  have hc : ((768963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((545103260403/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((768963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c200 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((9021/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3701159/10000000) (δ := 8049/1000000000) (ψ := 9749/10000) 157 132
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t200 : ((398454231/62500000000 : ℚ) : ℝ) ≤ stT157 200 := by
  have hc : ((1127/12500 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((398454231/62500000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((1127/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c201 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-638633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 707349/1250000) (δ := 8049/1000000000) (ψ := 9749/10000) 157 132
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t201 : ((-225246249659/5000000000000 : ℚ) : ℝ) ≤ stT157 201 := by
  have hc : ((-638683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225246249659/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-638683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c202 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-99511/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7606651/10000000) (δ := 3977/500000000) (ψ := 9749/10000) 157 132
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t202 : ((-8752407321/125000000000 : ℚ) : ℝ) ≤ stT157 202 := by
  have hc : ((-24879/25000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8752407321/125000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-24879/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c203 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-779843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6163029/10000000) (δ := 1989/250000000) (ψ := 9749/10000) 157 133
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t203 : ((-547378040659/10000000000000 : ℚ) : ℝ) ≤ stT157 203 := by
  have hc : ((-779893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547378040659/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-779893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c204 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-7663/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1058571/2500000) (δ := 1989/250000000) (ψ := 9749/10000) 157 133
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t204 : ((-42938947389/5000000000000 : ℚ) : ℝ) ≤ stT157 204 := by
  have hc : ((-61329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42938947389/5000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-61329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c205 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((601049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2314959/10000000) (δ := 1989/250000000) (ψ := 9749/10000) 157 133
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t205 : ((41975573157/1000000000000 : ℚ) : ℝ) ≤ stT157 205 := by
  have hc : ((600999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41975573157/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((600999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c206 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((246727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25311/625000) (δ := 7947/1000000000) (ψ := 9749/10000) 157 133
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t206 : ((343788267457/5000000000000 : ℚ) : ℝ) ≤ stT157 206 := by
  have hc : ((493429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((343788267457/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((493429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c207 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((165259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 299149/2000000) (δ := 1989/250000000) (ψ := 9749/10000) 157 133
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t207 : ((14356998369/250000000000 : ℚ) : ℝ) ≤ stT157 207 := by
  have hc : ((165249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14356998369/250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((165249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c208 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((53549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84683/250000) (δ := 491/62500000) (ψ := 9749/10000) 157 133
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t208 : ((593933931/40000000000 : ℚ) : ℝ) ≤ stT157 208 := by
  have hc : ((107073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((593933931/40000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((107073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c209 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-127919/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1317457/2500000) (δ := 8047/1000000000) (ψ := 9749/10000) 157 133
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t209 : ((-35396855009/1000000000000 : ℚ) : ℝ) ≤ stT157 209 := by
  have hc : ((-255863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35396855009/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-255863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c210 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-959871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7143349/10000000) (δ := 1989/250000000) (ψ := 9749/10000) 157 133
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t210 : ((-331204422393/5000000000000 : ℚ) : ℝ) ≤ stT157 210 := by
  have hc : ((-959921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331204422393/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-959921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c211 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-179069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1675001/2500000) (δ := 983/125000000) (ψ := 9749/10000) 157 134
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t211 : ((-123283176891/2000000000000 : ℚ) : ℝ) ≤ stT157 211 := by
  have hc : ((-179079/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123283176891/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-179079/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c212 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-179359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193769/400000) (δ := 7939/1000000000) (ψ := 9749/10000) 157 134
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t212 : ((-15400183669/625000000000 : ℚ) : ℝ) ≤ stT157 212 := by
  have hc : ((-22423/62500 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15400183669/625000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-22423/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c213 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((363417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2997159/10000000) (δ := 983/125000000) (ψ := 9749/10000) 157 134
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t213 : ((62243676999/2500000000000 : ℚ) : ℝ) ≤ stT157 213 := by
  have hc : ((363367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62243676999/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((363367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c214 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((894497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144841/1250000) (δ := 1991/250000000) (ψ := 9749/10000) 157 134
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t214 : ((122286110499/2000000000000 : ℚ) : ℝ) ≤ stT157 214 := by
  have hc : ((894447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122286110499/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((894447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c215 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((192837/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 671107/10000000) (δ := 1991/250000000) (ψ := 9749/10000) 157 134
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t215 : ((65753428519/1000000000000 : ℚ) : ℝ) ≤ stT157 215 := by
  have hc : ((192827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65753428519/1000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((192827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c216 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((135709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155779/625000) (δ := 1991/250000000) (ψ := 9749/10000) 157 134
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t216 : ((184659325309/5000000000000 : ℚ) : ℝ) ≤ stT157 216 := by
  have hc : ((271393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184659325309/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((271393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c217 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-150779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2152691/5000000) (δ := 983/125000000) (ψ := 9749/10000) 157 134
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t217 : ((-20477902501/2000000000000 : ℚ) : ℝ) ≤ stT157 217 := by
  have hc : ((-150829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20477902501/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-150829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c218 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-153277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6109979/10000000) (δ := 7939/1000000000) (ψ := 9749/10000) 157 134
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t218 : ((-51909569541/1000000000000 : ℚ) : ℝ) ≤ stT157 218 := by
  have hc : ((-153287/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51909569541/1000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-153287/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c219 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-999781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7801629/10000000) (δ := 7971/1000000000) (ψ := 9749/10000) 157 135
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t219 : ((-337811900139/5000000000000 : ℚ) : ℝ) ≤ stT157 219 := by
  have hc : ((-999831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337811900139/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-999831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c220 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-29641/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3006739/5000000) (δ := 1983/250000000) (ψ := 9749/10000) 157 135
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t220 : ((-99926553/2000000000 : ℚ) : ℝ) ≤ stT157 220 := by
  have hc : ((-29643/40000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99926553/2000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-29643/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c221 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-61131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1058353/2500000) (δ := 1983/250000000) (ψ := 9749/10000) 157 135
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t221 : ((-10284497497/1250000000000 : ℚ) : ℝ) ≤ stT157 221 := by
  have hc : ((-15289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10284497497/1250000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-15289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c222 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((553219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2461431/10000000) (δ := 7971/1000000000) (ψ := 9749/10000) 157 135
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t222 : ((92815673341/2500000000000 : ℚ) : ℝ) ≤ stT157 222 := by
  have hc : ((553169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92815673341/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((553169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c223 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((192269/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -697379/10000000) (δ := 7971/1000000000) (ψ := 9749/10000) 157 135
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t223 : ((128746047091/2000000000000 : ℚ) : ℝ) ≤ stT157 223 := by
  have hc : ((192259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128746047091/2000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((192259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c224 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((911651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1058783/10000000) (δ := 251/31250000) (ψ := 9749/10000) 157 135
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t224 : ((609088942953/10000000000000 : ℚ) : ℝ) ≤ stT157 224 := by
  have hc : ((911601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((609088942953/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((911601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c225 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((54139/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 561427/2000000) (δ := 251/31250000) (ψ := 9749/10000) 157 135
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t225 : ((72176927823/2500000000000 : ℚ) : ℝ) ≤ stT157 225 := by
  have hc : ((216531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72176927823/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((216531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c226 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-245739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284231/625000) (δ := 1979/125000000) (ψ := 9749/10000) 157 135
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t226 : ((-163496630699/10000000000000 : ℚ) : ℝ) ≤ stT157 226 := by
  have hc : ((-245789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163496630699/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-245789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c227 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-808409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6280603/10000000) (δ := 251/31250000) (ψ := 9749/10000) 157 135
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t227 : ((-134148410329/2500000000000 : ℚ) : ℝ) ≤ stT157 227 := by
  have hc : ((-808459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134148410329/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-808459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c228 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-199631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7702087/10000000) (δ := 317/40000000) (ψ := 9749/10000) 157 136
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t228 : ((-132215646147/2000000000000 : ℚ) : ℝ) ≤ stT157 228 := by
  have hc : ((-199641/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132215646147/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-199641/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c229 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-733151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119687/200000) (δ := 317/40000000) (ψ := 9749/10000) 157 136
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t229 : ((-484513151619/10000000000000 : ℚ) : ℝ) ≤ stT157 229 := by
  have hc : ((-733201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484513151619/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-733201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c230 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-69201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -427411/1000000) (δ := 321/40000000) (ψ := 9749/10000) 157 136
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t230 : ((-22823154553/2500000000000 : ℚ) : ℝ) ≤ stT157 230 := by
  have hc : ((-34613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22823154553/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-34613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c231 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((516091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321411/1250000) (δ := 321/40000000) (ψ := 9749/10000) 157 136
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t231 : ((339529691991/10000000000000 : ℚ) : ℝ) ≤ stT157 231 := by
  have hc : ((516041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339529691991/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((516041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c232 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((939257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175169/2000000) (δ := 321/40000000) (ψ := 9749/10000) 157 136
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t232 : ((154154862531/2500000000000 : ℚ) : ℝ) ≤ stT157 232 := by
  have hc : ((939207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154154862531/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((939207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c233 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((118459/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 812337/10000000) (δ := 317/40000000) (ψ := 9749/10000) 157 136
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t233 : ((310403536131/5000000000000 : ℚ) : ℝ) ≤ stT157 233 := by
  have hc : ((473811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310403536131/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((473811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c234 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((542557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2493297/10000000) (δ := 3939/500000000) (ψ := 9749/10000) 157 136
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t234 : ((8866191901/250000000000 : ℚ) : ℝ) ≤ stT157 234 := by
  have hc : ((542507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8866191901/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((542507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c235 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-47943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2083537/5000000) (δ := 3939/500000000) (ψ := 9749/10000) 157 136
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t235 : ((-977841171/156250000000 : ℚ) : ℝ) ≤ stT157 235 := by
  have hc : ((-1499/15625 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-977841171/156250000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-1499/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c236 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-345439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5833747/10000000) (δ := 3989/500000000) (ψ := 9749/10000) 157 136
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t236 : ((-5621951587/125000000000 : ℚ) : ℝ) ≤ stT157 236 := by
  have hc : ((-43183/62500 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5621951587/125000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-43183/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c237 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-494807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3746677/5000000) (δ := 321/40000000) (ψ := 9749/10000) 157 136
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t237 : ((-2008925139/31250000000 : ℚ) : ℝ) ≤ stT157 237 := by
  have hc : ((-30927/31250 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2008925139/31250000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-30927/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c238 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-434703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1640497/2500000) (δ := 4009/500000000) (ψ := 9749/10000) 157 137
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t238 : ((-8806013391/156250000000 : ℚ) : ℝ) ≤ stT157 238 := by
  have hc : ((-54341/62500 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8806013391/156250000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-54341/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c239 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-192733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2458137/5000000) (δ := 1597/200000000) (ψ := 9749/10000) 157 137
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t239 : ((-62342467013/2500000000000 : ℚ) : ℝ) ≤ stT157 239 := by
  have hc : ((-96379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62342467013/2500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-96379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c240 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((256911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -327743/1000000) (δ := 3959/500000000) (ψ := 9749/10000) 157 137
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t240 : ((165803004917/10000000000000 : ℚ) : ℝ) ≤ stT157 240 := by
  have hc : ((256861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165803004917/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((256861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c241 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((158223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329083/2000000) (δ := 3959/500000000) (ψ := 9749/10000) 157 137
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t241 : ((25478463307/500000000000 : ℚ) : ℝ) ≤ stT157 241 := by
  have hc : ((158213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25478463307/500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((158213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c242 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((31249/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20151/10000000) (δ := 3959/500000000) (ψ := 9749/10000) 157 137
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t242 : ((40173205527/625000000000 : ℚ) : ℝ) ≤ stT157 242 := by
  have hc : ((499959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40173205527/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((499959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c243 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((401239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1598401/10000000) (δ := 4009/500000000) (ψ := 9749/10000) 157 137
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t243 : ((257378781/5000000000 : ℚ) : ℝ) ≤ stT157 243 := by
  have hc : ((200607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257378781/5000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((200607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c244 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((141379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40129/125000) (δ := 4009/500000000) (ψ := 9749/10000) 157 137
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t244 : ((5655785571/312500000000 : ℚ) : ℝ) ≤ stT157 244 := by
  have hc : ((70677/250000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5655785571/312500000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((70677/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c245 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-21751/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2407813/5000000) (δ := 3157/200000000) (ψ := 9749/10000) 157 137
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t245 : ((-111185680941/5000000000000 : ℚ) : ℝ) ≤ stT157 245 := by
  have hc : ((-174033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111185680941/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-174033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c246 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-838743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400901/625000) (δ := 1597/200000000) (ψ := 9749/10000) 157 137
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t246 : ((-534795124561/10000000000000 : ℚ) : ℝ) ≤ stT157 246 := by
  have hc : ((-838793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534795124561/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-838793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c247 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-199627/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3850627/5000000) (δ := 8011/1000000000) (ψ := 9749/10000) 157 138
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t247 : ((-25405205709/400000000000 : ℚ) : ℝ) ≤ stT157 247 := by
  have hc : ((-199637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25405205709/400000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-199637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c248 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-23993/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6115397/10000000) (δ := 8011/1000000000) (ψ := 9749/10000) 157 138
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t248 : ((-243785138913/5000000000000 : ℚ) : ℝ) ≤ stT157 248 := by
  have hc : ((-383913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243785138913/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-383913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c249 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-241177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4535937/10000000) (δ := 999/125000000) (ψ := 9749/10000) 157 138
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t249 : ((-6114863223/400000000000 : ℚ) : ℝ) ≤ stT157 249 := by
  have hc : ((-241227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6114863223/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-241227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_c250 :
    |Real.cos (((157 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((376201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481379/5000000) (δ := 1973/250000000) (ψ := 9749/10000) 157 138
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st157_t250 : ((47579716141/2000000000000 : ℚ) : ℝ) ≤ stT157 250 := by
  have hc : ((376151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((157 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((9749/10000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st157_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47579716141/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((376151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st157_p1 : ((561201/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT157 (i+1) := by
  rw [Finset.sum_range_one]
  exact st157_t1

theorem st157_p2 : ((9221301799877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT157 (i+1))
      = (∑ i ∈ Finset.range 1, stT157 (i+1)) + stT157 2 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 1
    simpa using h
  have hprev := st157_p1
  have hstep := st157_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p3 : ((7567724352653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT157 (i+1))
      = (∑ i ∈ Finset.range 2, stT157 (i+1)) + stT157 3 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 2
    simpa using h
  have hprev := st157_p2
  have hstep := st157_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p4 : ((2590773357263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT157 (i+1))
      = (∑ i ∈ Finset.range 3, stT157 (i+1)) + stT157 4 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 3
    simpa using h
  have hprev := st157_p3
  have hstep := st157_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p5 : ((6744581787963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT157 (i+1))
      = (∑ i ∈ Finset.range 4, stT157 (i+1)) + stT157 5 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 4
    simpa using h
  have hprev := st157_p4
  have hstep := st157_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p6 : ((1850547396973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT157 (i+1))
      = (∑ i ∈ Finset.range 5, stT157 (i+1)) + stT157 6 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 5
    simpa using h
  have hprev := st157_p5
  have hstep := st157_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p7 : ((-2273190309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT157 (i+1))
      = (∑ i ∈ Finset.range 6, stT157 (i+1)) + stT157 7 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 6
    simpa using h
  have hprev := st157_p6
  have hstep := st157_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p8 : ((1185213349467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT157 (i+1))
      = (∑ i ∈ Finset.range 7, stT157 (i+1)) + stT157 8 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 7
    simpa using h
  have hprev := st157_p7
  have hstep := st157_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p9 : ((1134910006073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT157 (i+1))
      = (∑ i ∈ Finset.range 8, stT157 (i+1)) + stT157 9 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 8
    simpa using h
  have hprev := st157_p8
  have hstep := st157_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p10 : ((-234859846307/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT157 (i+1))
      = (∑ i ∈ Finset.range 9, stT157 (i+1)) + stT157 10 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 9
    simpa using h
  have hprev := st157_p9
  have hstep := st157_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p11 : ((-950535635353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT157 (i+1))
      = (∑ i ∈ Finset.range 10, stT157 (i+1)) + stT157 11 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 10
    simpa using h
  have hprev := st157_p10
  have hstep := st157_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p12 : ((170589016261/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT157 (i+1))
      = (∑ i ∈ Finset.range 11, stT157 (i+1)) + stT157 12 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 11
    simpa using h
  have hprev := st157_p11
  have hstep := st157_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p13 : ((425846147311/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT157 (i+1))
      = (∑ i ∈ Finset.range 12, stT157 (i+1)) + stT157 13 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 12
    simpa using h
  have hprev := st157_p12
  have hstep := st157_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p14 : ((2443782469589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT157 (i+1))
      = (∑ i ∈ Finset.range 13, stT157 (i+1)) + stT157 14 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 13
    simpa using h
  have hprev := st157_p13
  have hstep := st157_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p15 : ((2312508579643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT157 (i+1))
      = (∑ i ∈ Finset.range 14, stT157 (i+1)) + stT157 15 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 14
    simpa using h
  have hprev := st157_p14
  have hstep := st157_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p16 : ((4086591079643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT157 (i+1))
      = (∑ i ∈ Finset.range 15, stT157 (i+1)) + stT157 16 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 15
    simpa using h
  have hprev := st157_p15
  have hstep := st157_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p17 : ((2531883884789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT157 (i+1))
      = (∑ i ∈ Finset.range 16, stT157 (i+1)) + stT157 17 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 16
    simpa using h
  have hprev := st157_p16
  have hstep := st157_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p18 : ((4679955884489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT157 (i+1))
      = (∑ i ∈ Finset.range 17, stT157 (i+1)) + stT157 18 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 17
    simpa using h
  have hprev := st157_p17
  have hstep := st157_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p19 : ((2679989235619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT157 (i+1))
      = (∑ i ∈ Finset.range 18, stT157 (i+1)) + stT157 19 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 18
    simpa using h
  have hprev := st157_p18
  have hstep := st157_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p20 : ((1991278055551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT157 (i+1))
      = (∑ i ∈ Finset.range 19, stT157 (i+1)) + stT157 20 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 19
    simpa using h
  have hprev := st157_p19
  have hstep := st157_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p21 : ((3898883508701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT157 (i+1))
      = (∑ i ∈ Finset.range 20, stT157 (i+1)) + stT157 21 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 20
    simpa using h
  have hprev := st157_p20
  have hstep := st157_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p22 : ((2877912680791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT157 (i+1))
      = (∑ i ∈ Finset.range 21, stT157 (i+1)) + stT157 22 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 21
    simpa using h
  have hprev := st157_p21
  have hstep := st157_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p23 : ((649329283607/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT157 (i+1))
      = (∑ i ∈ Finset.range 22, stT157 (i+1)) + stT157 23 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 22
    simpa using h
  have hprev := st157_p22
  have hstep := st157_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p24 : ((128348805667/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT157 (i+1))
      = (∑ i ∈ Finset.range 23, stT157 (i+1)) + stT157 24 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 23
    simpa using h
  have hprev := st157_p23
  have hstep := st157_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p25 : ((6092806121033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT157 (i+1))
      = (∑ i ∈ Finset.range 24, stT157 (i+1)) + stT157 25 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 24
    simpa using h
  have hprev := st157_p24
  have hstep := st157_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p26 : ((6019276274167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT157 (i+1))
      = (∑ i ∈ Finset.range 25, stT157 (i+1)) + stT157 26 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 25
    simpa using h
  have hprev := st157_p25
  have hstep := st157_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p27 : ((6625488000667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT157 (i+1))
      = (∑ i ∈ Finset.range 26, stT157 (i+1)) + stT157 27 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 26
    simpa using h
  have hprev := st157_p26
  have hstep := st157_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p28 : ((8098623147887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT157 (i+1))
      = (∑ i ∈ Finset.range 27, stT157 (i+1)) + stT157 28 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 27
    simpa using h
  have hprev := st157_p27
  have hstep := st157_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p29 : ((9946751907231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT157 (i+1))
      = (∑ i ∈ Finset.range 28, stT157 (i+1)) + stT157 29 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 28
    simpa using h
  have hprev := st157_p28
  have hstep := st157_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p30 : ((10842927831527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT157 (i+1))
      = (∑ i ∈ Finset.range 29, stT157 (i+1)) + stT157 30 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 29
    simpa using h
  have hprev := st157_p29
  have hstep := st157_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p31 : ((9796284547243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT157 (i+1))
      = (∑ i ∈ Finset.range 30, stT157 (i+1)) + stT157 31 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 30
    simpa using h
  have hprev := st157_p30
  have hstep := st157_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p32 : ((8135534625889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT157 (i+1))
      = (∑ i ∈ Finset.range 31, stT157 (i+1)) + stT157 32 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 31
    simpa using h
  have hprev := st157_p31
  have hstep := st157_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p33 : ((8534224553169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT157 (i+1))
      = (∑ i ∈ Finset.range 32, stT157 (i+1)) + stT157 33 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 32
    simpa using h
  have hprev := st157_p32
  have hstep := st157_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p34 : ((10192971765049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT157 (i+1))
      = (∑ i ∈ Finset.range 33, stT157 (i+1)) + stT157 34 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 33
    simpa using h
  have hprev := st157_p33
  have hstep := st157_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p35 : ((9506807729589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT157 (i+1))
      = (∑ i ∈ Finset.range 34, stT157 (i+1)) + stT157 35 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 34
    simpa using h
  have hprev := st157_p34
  have hstep := st157_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p36 : ((4120042904789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT157 (i+1))
      = (∑ i ∈ Finset.range 35, stT157 (i+1)) + stT157 36 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 35
    simpa using h
  have hprev := st157_p35
  have hstep := st157_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p37 : ((9718507033399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT157 (i+1))
      = (∑ i ∈ Finset.range 36, stT157 (i+1)) + stT157 37 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 36
    simpa using h
  have hprev := st157_p36
  have hstep := st157_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p38 : ((4800101880047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT157 (i+1))
      = (∑ i ∈ Finset.range 37, stT157 (i+1)) + stT157 38 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 37
    simpa using h
  have hprev := st157_p37
  have hstep := st157_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p39 : ((2095707680219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT157 (i+1))
      = (∑ i ∈ Finset.range 38, stT157 (i+1)) + stT157 39 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 38
    simpa using h
  have hprev := st157_p38
  have hstep := st157_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p40 : ((4975665342421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT157 (i+1))
      = (∑ i ∈ Finset.range 39, stT157 (i+1)) + stT157 40 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 39
    simpa using h
  have hprev := st157_p39
  have hstep := st157_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p41 : ((893382089613/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT157 (i+1))
      = (∑ i ∈ Finset.range 40, stT157 (i+1)) + stT157 41 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 40
    simpa using h
  have hprev := st157_p40
  have hstep := st157_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p42 : ((9038273428999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT157 (i+1))
      = (∑ i ∈ Finset.range 41, stT157 (i+1)) + stT157 42 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 41
    simpa using h
  have hprev := st157_p41
  have hstep := st157_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p43 : ((4874512356467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT157 (i+1))
      = (∑ i ∈ Finset.range 42, stT157 (i+1)) + stT157 43 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 42
    simpa using h
  have hprev := st157_p42
  have hstep := st157_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p44 : ((2130087670591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT157 (i+1))
      = (∑ i ∈ Finset.range 43, stT157 (i+1)) + stT157 44 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 43
    simpa using h
  have hprev := st157_p43
  have hstep := st157_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p45 : ((9971219449467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT157 (i+1))
      = (∑ i ∈ Finset.range 44, stT157 (i+1)) + stT157 45 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 44
    simpa using h
  have hprev := st157_p44
  have hstep := st157_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p46 : ((8501162258247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT157 (i+1))
      = (∑ i ∈ Finset.range 45, stT157 (i+1)) + stT157 46 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 45
    simpa using h
  have hprev := st157_p45
  have hstep := st157_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p47 : ((38629286771/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT157 (i+1))
      = (∑ i ∈ Finset.range 46, stT157 (i+1)) + stT157 47 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 46
    simpa using h
  have hprev := st157_p46
  have hstep := st157_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p48 : ((537893111031/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT157 (i+1))
      = (∑ i ∈ Finset.range 47, stT157 (i+1)) + stT157 48 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 47
    simpa using h
  have hprev := st157_p47
  have hstep := st157_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p49 : ((4903731850929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT157 (i+1))
      = (∑ i ∈ Finset.range 48, stT157 (i+1)) + stT157 49 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 48
    simpa using h
  have hprev := st157_p48
  have hstep := st157_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p50 : ((2160478090923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT157 (i+1))
      = (∑ i ∈ Finset.range 49, stT157 (i+1)) + stT157 50 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 49
    simpa using h
  have hprev := st157_p49
  have hstep := st157_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p51 : ((2455266786873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT157 (i+1))
      = (∑ i ∈ Finset.range 50, stT157 (i+1)) + stT157 51 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 50
    simpa using h
  have hprev := st157_p50
  have hstep := st157_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p52 : ((8588796048639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT157 (i+1))
      = (∑ i ∈ Finset.range 51, stT157 (i+1)) + stT157 52 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 51
    simpa using h
  have hprev := st157_p51
  have hstep := st157_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p53 : ((9890165908899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT157 (i+1))
      = (∑ i ∈ Finset.range 52, stT157 (i+1)) + stT157 53 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 52
    simpa using h
  have hprev := st157_p52
  have hstep := st157_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p54 : ((1707767841999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT157 (i+1))
      = (∑ i ∈ Finset.range 53, stT157 (i+1)) + stT157 54 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 53
    simpa using h
  have hprev := st157_p53
  have hstep := st157_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p55 : ((617098430183/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT157 (i+1))
      = (∑ i ∈ Finset.range 54, stT157 (i+1)) + stT157 55 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 54
    simpa using h
  have hprev := st157_p54
  have hstep := st157_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p56 : ((8673046028277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT157 (i+1))
      = (∑ i ∈ Finset.range 55, stT157 (i+1)) + stT157 56 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 55
    simpa using h
  have hprev := st157_p55
  have hstep := st157_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p57 : ((9578954391549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT157 (i+1))
      = (∑ i ∈ Finset.range 56, stT157 (i+1)) + stT157 57 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 56
    simpa using h
  have hprev := st157_p56
  have hstep := st157_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p58 : ((9138342300149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT157 (i+1))
      = (∑ i ∈ Finset.range 57, stT157 (i+1)) + stT157 58 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 57
    simpa using h
  have hprev := st157_p57
  have hstep := st157_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p59 : ((8988080760129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT157 (i+1))
      = (∑ i ∈ Finset.range 58, stT157 (i+1)) + stT157 59 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 58
    simpa using h
  have hprev := st157_p58
  have hstep := st157_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p60 : ((9736555187533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT157 (i+1))
      = (∑ i ∈ Finset.range 59, stT157 (i+1)) + stT157 60 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 59
    simpa using h
  have hprev := st157_p59
  have hstep := st157_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p61 : ((214002619417/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT157 (i+1))
      = (∑ i ∈ Finset.range 60, stT157 (i+1)) + stT157 61 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 60
    simpa using h
  have hprev := st157_p60
  have hstep := st157_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p62 : ((613053824997/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT157 (i+1))
      = (∑ i ∈ Finset.range 61, stT157 (i+1)) + stT157 62 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 61
    simpa using h
  have hprev := st157_p61
  have hstep := st157_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p63 : ((894232569929/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT157 (i+1))
      = (∑ i ∈ Finset.range 62, stT157 (i+1)) + stT157 63 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 62
    simpa using h
  have hprev := st157_p62
  have hstep := st157_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p64 : ((905369444929/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT157 (i+1))
      = (∑ i ∈ Finset.range 63, stT157 (i+1)) + stT157 64 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 63
    simpa using h
  have hprev := st157_p63
  have hstep := st157_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p65 : ((1954493866811/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT157 (i+1))
      = (∑ i ∈ Finset.range 64, stT157 (i+1)) + stT157 65 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 64
    simpa using h
  have hprev := st157_p64
  have hstep := st157_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p66 : ((428401627331/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT157 (i+1))
      = (∑ i ∈ Finset.range 65, stT157 (i+1)) + stT157 66 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 65
    simpa using h
  have hprev := st157_p65
  have hstep := st157_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p67 : ((4797395915143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT157 (i+1))
      = (∑ i ∈ Finset.range 66, stT157 (i+1)) + stT157 67 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 66
    simpa using h
  have hprev := st157_p66
  have hstep := st157_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p68 : ((9374568111207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT157 (i+1))
      = (∑ i ∈ Finset.range 67, stT157 (i+1)) + stT157 68 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 67
    simpa using h
  have hprev := st157_p67
  have hstep := st157_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p69 : ((8629745363343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT157 (i+1))
      = (∑ i ∈ Finset.range 68, stT157 (i+1)) + stT157 69 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 68
    simpa using h
  have hprev := st157_p68
  have hstep := st157_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p70 : ((9824644675643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT157 (i+1))
      = (∑ i ∈ Finset.range 69, stT157 (i+1)) + stT157 70 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 69
    simpa using h
  have hprev := st157_p69
  have hstep := st157_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p71 : ((9080749542749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT157 (i+1))
      = (∑ i ∈ Finset.range 70, stT157 (i+1)) + stT157 71 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 70
    simpa using h
  have hprev := st157_p70
  have hstep := st157_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p72 : ((1753644696201/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT157 (i+1))
      = (∑ i ∈ Finset.range 71, stT157 (i+1)) + stT157 72 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 71
    simpa using h
  have hprev := st157_p71
  have hstep := st157_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p73 : ((4938389715033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT157 (i+1))
      = (∑ i ∈ Finset.range 72, stT157 (i+1)) + stT157 73 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 72
    simpa using h
  have hprev := st157_p72
  have hstep := st157_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p74 : ((358886383631/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT157 (i+1))
      = (∑ i ∈ Finset.range 73, stT157 (i+1)) + stT157 74 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 73
    simpa using h
  have hprev := st157_p73
  have hstep := st157_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p75 : ((8808138932529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT157 (i+1))
      = (∑ i ∈ Finset.range 74, stT157 (i+1)) + stT157 75 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 74
    simpa using h
  have hprev := st157_p74
  have hstep := st157_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p76 : ((1975818679043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT157 (i+1))
      = (∑ i ∈ Finset.range 75, stT157 (i+1)) + stT157 76 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 75
    simpa using h
  have hprev := st157_p75
  have hstep := st157_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p77 : ((9024570092569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT157 (i+1))
      = (∑ i ∈ Finset.range 76, stT157 (i+1)) + stT157 77 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 76
    simpa using h
  have hprev := st157_p76
  have hstep := st157_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p78 : ((8724668147821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT157 (i+1))
      = (∑ i ∈ Finset.range 77, stT157 (i+1)) + stT157 78 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 77
    simpa using h
  have hprev := st157_p77
  have hstep := st157_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p79 : ((4917554945171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT157 (i+1))
      = (∑ i ∈ Finset.range 78, stT157 (i+1)) + stT157 79 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 78
    simpa using h
  have hprev := st157_p78
  have hstep := st157_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p80 : ((4618083948101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT157 (i+1))
      = (∑ i ∈ Finset.range 79, stT157 (i+1)) + stT157 80 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 79
    simpa using h
  have hprev := st157_p79
  have hstep := st157_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p81 : ((4292564798797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT157 (i+1))
      = (∑ i ∈ Finset.range 80, stT157 (i+1)) + stT157 81 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 80
    simpa using h
  have hprev := st157_p80
  have hstep := st157_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p82 : ((4824637017577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT157 (i+1))
      = (∑ i ∈ Finset.range 81, stT157 (i+1)) + stT157 82 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 81
    simpa using h
  have hprev := st157_p81
  have hstep := st157_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p83 : ((1916263132819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT157 (i+1))
      = (∑ i ∈ Finset.range 82, stT157 (i+1)) + stT157 83 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 82
    simpa using h
  have hprev := st157_p82
  have hstep := st157_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p84 : ((1712909270107/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT157 (i+1))
      = (∑ i ∈ Finset.range 83, stT157 (i+1)) + stT157 84 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 83
    simpa using h
  have hprev := st157_p83
  have hstep := st157_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p85 : ((9228287210763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT157 (i+1))
      = (∑ i ∈ Finset.range 84, stT157 (i+1)) + stT157 85 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 84
    simpa using h
  have hprev := st157_p84
  have hstep := st157_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p86 : ((9878026674651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT157 (i+1))
      = (∑ i ∈ Finset.range 85, stT157 (i+1)) + stT157 86 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 85
    simpa using h
  have hprev := st157_p85
  have hstep := st157_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p87 : ((1778306094921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT157 (i+1))
      = (∑ i ∈ Finset.range 86, stT157 (i+1)) + stT157 87 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 86
    simpa using h
  have hprev := st157_p86
  have hstep := st157_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p88 : ((8701708208329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT157 (i+1))
      = (∑ i ∈ Finset.range 87, stT157 (i+1)) + stT157 88 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 87
    simpa using h
  have hprev := st157_p87
  have hstep := st157_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p89 : ((9761340569361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT157 (i+1))
      = (∑ i ∈ Finset.range 88, stT157 (i+1)) + stT157 89 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 88
    simpa using h
  have hprev := st157_p88
  have hstep := st157_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p90 : ((2385990060109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT157 (i+1))
      = (∑ i ∈ Finset.range 89, stT157 (i+1)) + stT157 90 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 89
    simpa using h
  have hprev := st157_p89
  have hstep := st157_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p91 : ((8567207063981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT157 (i+1))
      = (∑ i ∈ Finset.range 90, stT157 (i+1)) + stT157 91 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 90
    simpa using h
  have hprev := st157_p90
  have hstep := st157_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p92 : ((9082253270561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT157 (i+1))
      = (∑ i ∈ Finset.range 91, stT157 (i+1)) + stT157 92 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 91
    simpa using h
  have hprev := st157_p91
  have hstep := st157_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p93 : ((9911903248347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT157 (i+1))
      = (∑ i ∈ Finset.range 92, stT157 (i+1)) + stT157 93 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 92
    simpa using h
  have hprev := st157_p92
  have hstep := st157_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p94 : ((9207557541611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT157 (i+1))
      = (∑ i ∈ Finset.range 93, stT157 (i+1)) + stT157 94 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 93
    simpa using h
  have hprev := st157_p93
  have hstep := st157_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p95 : ((8524411476419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT157 (i+1))
      = (∑ i ∈ Finset.range 94, stT157 (i+1)) + stT157 95 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 94
    simpa using h
  have hprev := st157_p94
  have hstep := st157_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p96 : ((9333533496919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT157 (i+1))
      = (∑ i ∈ Finset.range 95, stT157 (i+1)) + stT157 96 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 95
    simpa using h
  have hprev := st157_p95
  have hstep := st157_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p97 : ((9906121628083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT157 (i+1))
      = (∑ i ∈ Finset.range 96, stT157 (i+1)) + stT157 97 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 96
    simpa using h
  have hprev := st157_p96
  have hstep := st157_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p98 : ((9050067468233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT157 (i+1))
      = (∑ i ∈ Finset.range 97, stT157 (i+1)) + stT157 98 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 97
    simpa using h
  have hprev := st157_p97
  have hstep := st157_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p99 : ((8536226715163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT157 (i+1))
      = (∑ i ∈ Finset.range 98, stT157 (i+1)) + stT157 99 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 98
    simpa using h
  have hprev := st157_p98
  have hstep := st157_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p100 : ((1174904606519/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT157 (i+1))
      = (∑ i ∈ Finset.range 99, stT157 (i+1)) + stT157 100 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 99
    simpa using h
  have hprev := st157_p99
  have hstep := st157_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p101 : ((1981826523479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT157 (i+1))
      = (∑ i ∈ Finset.range 100, stT157 (i+1)) + stT157 101 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 100
    simpa using h
  have hprev := st157_p100
  have hstep := st157_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p102 : ((9071263438907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT157 (i+1))
      = (∑ i ∈ Finset.range 101, stT157 (i+1)) + stT157 102 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 101
    simpa using h
  have hprev := st157_p101
  have hstep := st157_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p103 : ((8513916451057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT157 (i+1))
      = (∑ i ∈ Finset.range 102, stT157 (i+1)) + stT157 103 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 102
    simpa using h
  have hprev := st157_p102
  have hstep := st157_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p104 : ((9291494818297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT157 (i+1))
      = (∑ i ∈ Finset.range 103, stT157 (i+1)) + stT157 104 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 103
    simpa using h
  have hprev := st157_p103
  have hstep := st157_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p105 : ((9937443028297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT157 (i+1))
      = (∑ i ∈ Finset.range 104, stT157 (i+1)) + stT157 105 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 104
    simpa using h
  have hprev := st157_p104
  have hstep := st157_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p106 : ((9264925573183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT157 (i+1))
      = (∑ i ∈ Finset.range 105, stT157 (i+1)) + stT157 106 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 105
    simpa using h
  have hprev := st157_p105
  have hstep := st157_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p107 : ((4253006429879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT157 (i+1))
      = (∑ i ∈ Finset.range 106, stT157 (i+1)) + stT157 107 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 106
    simpa using h
  have hprev := st157_p106
  have hstep := st157_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p108 : ((1126915150001/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT157 (i+1))
      = (∑ i ∈ Finset.range 107, stT157 (i+1)) + stT157 108 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 107
    simpa using h
  have hprev := st157_p107
  have hstep := st157_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p109 : ((154441996349/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT157 (i+1))
      = (∑ i ∈ Finset.range 108, stT157 (i+1)) + stT157 109 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 108
    simpa using h
  have hprev := st157_p108
  have hstep := st157_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p110 : ((9605171961179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT157 (i+1))
      = (∑ i ∈ Finset.range 109, stT157 (i+1)) + stT157 110 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 109
    simpa using h
  have hprev := st157_p109
  have hstep := st157_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p111 : ((8666213613047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT157 (i+1))
      = (∑ i ∈ Finset.range 110, stT157 (i+1)) + stT157 111 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 110
    simpa using h
  have hprev := st157_p110
  have hstep := st157_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p112 : ((8651378494647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT157 (i+1))
      = (∑ i ∈ Finset.range 111, stT157 (i+1)) + stT157 112 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 111
    simpa using h
  have hprev := st157_p111
  have hstep := st157_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p113 : ((9574967042727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT157 (i+1))
      = (∑ i ∈ Finset.range 112, stT157 (i+1)) + stT157 113 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 112
    simpa using h
  have hprev := st157_p112
  have hstep := st157_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p114 : ((9920932175877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT157 (i+1))
      = (∑ i ∈ Finset.range 113, stT157 (i+1)) + stT157 114 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 113
    simpa using h
  have hprev := st157_p113
  have hstep := st157_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p115 : ((2284966263843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT157 (i+1))
      = (∑ i ∈ Finset.range 114, stT157 (i+1)) + stT157 115 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 114
    simpa using h
  have hprev := st157_p114
  have hstep := st157_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p116 : ((1060074763071/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT157 (i+1))
      = (∑ i ∈ Finset.range 115, stT157 (i+1)) + stT157 116 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 115
    simpa using h
  have hprev := st157_p115
  have hstep := st157_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p117 : ((1121273427321/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT157 (i+1))
      = (∑ i ∈ Finset.range 116, stT157 (i+1)) + stT157 117 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 116
    simpa using h
  have hprev := st157_p116
  have hstep := st157_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p118 : ((2460738082113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT157 (i+1))
      = (∑ i ∈ Finset.range 117, stT157 (i+1)) + stT157 118 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 117
    simpa using h
  have hprev := st157_p117
  have hstep := st157_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p119 : ((4885905492929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT157 (i+1))
      = (∑ i ∈ Finset.range 118, stT157 (i+1)) + stT157 119 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 118
    simpa using h
  have hprev := st157_p118
  have hstep := st157_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p120 : ((4436767483703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT157 (i+1))
      = (∑ i ∈ Finset.range 119, stT157 (i+1)) + stT157 120 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 119
    simpa using h
  have hprev := st157_p119
  have hstep := st157_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p121 : ((1060042547829/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT157 (i+1))
      = (∑ i ∈ Finset.range 120, stT157 (i+1)) + stT157 121 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 120
    simpa using h
  have hprev := st157_p120
  have hstep := st157_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p122 : ((9157454166861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT157 (i+1))
      = (∑ i ∈ Finset.range 121, stT157 (i+1)) + stT157 122 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 121
    simpa using h
  have hprev := st157_p121
  have hstep := st157_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p123 : ((4961677178593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT157 (i+1))
      = (∑ i ∈ Finset.range 122, stT157 (i+1)) + stT157 123 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 122
    simpa using h
  have hprev := st157_p122
  have hstep := st157_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p124 : ((4847841480019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT157 (i+1))
      = (∑ i ∈ Finset.range 123, stT157 (i+1)) + stT157 124 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 123
    simpa using h
  have hprev := st157_p123
  have hstep := st157_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p125 : ((7041990701/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT157 (i+1))
      = (∑ i ∈ Finset.range 124, stT157 (i+1)) + stT157 125 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 124
    simpa using h
  have hprev := st157_p124
  have hstep := st157_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p126 : ((8477585049937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT157 (i+1))
      = (∑ i ∈ Finset.range 125, stT157 (i+1)) + stT157 126 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 125
    simpa using h
  have hprev := st157_p125
  have hstep := st157_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p127 : ((9154535631997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT157 (i+1))
      = (∑ i ∈ Finset.range 126, stT157 (i+1)) + stT157 127 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 126
    simpa using h
  have hprev := st157_p126
  have hstep := st157_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p128 : ((991781368053/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT157 (i+1))
      = (∑ i ∈ Finset.range 127, stT157 (i+1)) + stT157 128 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 127
    simpa using h
  have hprev := st157_p127
  have hstep := st157_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p129 : ((1952126233151/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT157 (i+1))
      = (∑ i ∈ Finset.range 128, stT157 (i+1)) + stT157 129 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 128
    simpa using h
  have hprev := st157_p128
  have hstep := st157_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p130 : ((4448771419283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT157 (i+1))
      = (∑ i ∈ Finset.range 129, stT157 (i+1)) + stT157 130 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 129
    simpa using h
  have hprev := st157_p129
  have hstep := st157_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p131 : ((4221632583023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT157 (i+1))
      = (∑ i ∈ Finset.range 130, stT157 (i+1)) + stT157 131 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 130
    simpa using h
  have hprev := st157_p130
  have hstep := st157_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p132 : ((4484011480817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT157 (i+1))
      = (∑ i ∈ Finset.range 131, stT157 (i+1)) + stT157 132 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 131
    simpa using h
  have hprev := st157_p131
  have hstep := st157_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p133 : ((9805652856961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT157 (i+1))
      = (∑ i ∈ Finset.range 132, stT157 (i+1)) + stT157 133 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 132
    simpa using h
  have hprev := st157_p132
  have hstep := st157_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p134 : ((9920555075773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT157 (i+1))
      = (∑ i ∈ Finset.range 133, stT157 (i+1)) + stT157 134 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 133
    simpa using h
  have hprev := st157_p133
  have hstep := st157_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p135 : ((1836194717853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT157 (i+1))
      = (∑ i ∈ Finset.range 134, stT157 (i+1)) + stT157 135 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 134
    simpa using h
  have hprev := st157_p134
  have hstep := st157_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p136 : ((1060486154037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT157 (i+1))
      = (∑ i ∈ Finset.range 135, stT157 (i+1)) + stT157 136 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 135
    simpa using h
  have hprev := st157_p135
  have hstep := st157_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p137 : ((4327256434383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT157 (i+1))
      = (∑ i ∈ Finset.range 136, stT157 (i+1)) + stT157 137 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 136
    simpa using h
  have hprev := st157_p136
  have hstep := st157_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p138 : ((4741860669183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT157 (i+1))
      = (∑ i ∈ Finset.range 137, stT157 (i+1)) + stT157 138 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 137
    simpa using h
  have hprev := st157_p137
  have hstep := st157_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p139 : ((5003556777857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT157 (i+1))
      = (∑ i ∈ Finset.range 138, stT157 (i+1)) + stT157 139 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 138
    simpa using h
  have hprev := st157_p138
  have hstep := st157_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p140 : ((9631581608789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT157 (i+1))
      = (∑ i ∈ Finset.range 139, stT157 (i+1)) + stT157 140 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 139
    simpa using h
  have hprev := st157_p139
  have hstep := st157_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p141 : ((8789408554989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT157 (i+1))
      = (∑ i ∈ Finset.range 140, stT157 (i+1)) + stT157 141 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 140
    simpa using h
  have hprev := st157_p140
  have hstep := st157_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p142 : ((8421154513839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT157 (i+1))
      = (∑ i ∈ Finset.range 141, stT157 (i+1)) + stT157 142 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 141
    simpa using h
  have hprev := st157_p141
  have hstep := st157_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p143 : ((8925548092253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT157 (i+1))
      = (∑ i ∈ Finset.range 142, stT157 (i+1)) + stT157 143 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 142
    simpa using h
  have hprev := st157_p142
  have hstep := st157_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p144 : ((30458479991/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT157 (i+1))
      = (∑ i ∈ Finset.range 143, stT157 (i+1)) + stT157 144 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 143
    simpa using h
  have hprev := st157_p143
  have hstep := st157_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p145 : ((5001378341519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT157 (i+1))
      = (∑ i ∈ Finset.range 144, stT157 (i+1)) + stT157 145 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 144
    simpa using h
  have hprev := st157_p144
  have hstep := st157_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p146 : ((37716909521/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT157 (i+1))
      = (∑ i ∈ Finset.range 145, stT157 (i+1)) + stT157 146 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 145
    simpa using h
  have hprev := st157_p145
  have hstep := st157_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p147 : ((4316751287491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT157 (i+1))
      = (∑ i ∈ Finset.range 146, stT157 (i+1)) + stT157 147 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 146
    simpa using h
  have hprev := st157_p146
  have hstep := st157_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p148 : ((527382250467/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT157 (i+1))
      = (∑ i ∈ Finset.range 147, stT157 (i+1)) + stT157 148 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 147
    simpa using h
  have hprev := st157_p147
  have hstep := st157_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p149 : ((903554676807/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT157 (i+1))
      = (∑ i ∈ Finset.range 148, stT157 (i+1)) + stT157 149 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 148
    simpa using h
  have hprev := st157_p148
  have hstep := st157_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p150 : ((981633331551/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT157 (i+1))
      = (∑ i ∈ Finset.range 149, stT157 (i+1)) + stT157 150 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 149
    simpa using h
  have hprev := st157_p149
  have hstep := st157_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p151 : ((5001274584199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT157 (i+1))
      = (∑ i ∈ Finset.range 150, stT157 (i+1)) + stT157 151 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 150
    simpa using h
  have hprev := st157_p150
  have hstep := st157_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p152 : ((4708810128207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT157 (i+1))
      = (∑ i ∈ Finset.range 151, stT157 (i+1)) + stT157 152 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 151
    simpa using h
  have hprev := st157_p151
  have hstep := st157_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p153 : ((8637158324633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT157 (i+1))
      = (∑ i ∈ Finset.range 152, stT157 (i+1)) + stT157 153 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 152
    simpa using h
  have hprev := st157_p152
  have hstep := st157_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p154 : ((2102853968809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT157 (i+1))
      = (∑ i ∈ Finset.range 153, stT157 (i+1)) + stT157 154 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 153
    simpa using h
  have hprev := st157_p153
  have hstep := st157_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p155 : ((8948391070087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT157 (i+1))
      = (∑ i ∈ Finset.range 154, stT157 (i+1)) + stT157 155 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 154
    simpa using h
  have hprev := st157_p154
  have hstep := st157_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p156 : ((9737292887047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT157 (i+1))
      = (∑ i ∈ Finset.range 155, stT157 (i+1)) + stT157 156 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 155
    simpa using h
  have hprev := st157_p155
  have hstep := st157_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p157 : ((2009085661009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT157 (i+1))
      = (∑ i ∈ Finset.range 156, stT157 (i+1)) + stT157 157 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 156
    simpa using h
  have hprev := st157_p156
  have hstep := st157_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p158 : ((9595934852813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT157 (i+1))
      = (∑ i ∈ Finset.range 157, stT157 (i+1)) + stT157 158 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 157
    simpa using h
  have hprev := st157_p157
  have hstep := st157_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p159 : ((8803004189769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT157 (i+1))
      = (∑ i ∈ Finset.range 158, stT157 (i+1)) + stT157 159 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 158
    simpa using h
  have hprev := st157_p158
  have hstep := st157_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p160 : ((8378784327769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT157 (i+1))
      = (∑ i ∈ Finset.range 159, stT157 (i+1)) + stT157 160 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 159
    simpa using h
  have hprev := st157_p159
  have hstep := st157_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p161 : ((8694226143379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT157 (i+1))
      = (∑ i ∈ Finset.range 160, stT157 (i+1)) + stT157 161 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 160
    simpa using h
  have hprev := st157_p160
  have hstep := st157_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p162 : ((9466191703427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT157 (i+1))
      = (∑ i ∈ Finset.range 161, stT157 (i+1)) + stT157 162 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 161
    simpa using h
  have hprev := st157_p161
  have hstep := st157_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p163 : ((10023337856847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT157 (i+1))
      = (∑ i ∈ Finset.range 162, stT157 (i+1)) + stT157 163 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 162
    simpa using h
  have hprev := st157_p162
  have hstep := st157_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p164 : ((9892111259659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT157 (i+1))
      = (∑ i ∈ Finset.range 163, stT157 (i+1)) + stT157 164 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 163
    simpa using h
  have hprev := st157_p163
  have hstep := st157_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p165 : ((9190261714201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT157 (i+1))
      = (∑ i ∈ Finset.range 164, stT157 (i+1)) + stT157 165 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 164
    simpa using h
  have hprev := st157_p164
  have hstep := st157_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p166 : ((4254738581861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT157 (i+1))
      = (∑ i ∈ Finset.range 165, stT157 (i+1)) + stT157 166 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 165
    simpa using h
  have hprev := st157_p165
  have hstep := st157_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p167 : ((4205794600773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT157 (i+1))
      = (∑ i ∈ Finset.range 166, stT157 (i+1)) + stT157 167 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 166
    simpa using h
  have hprev := st157_p166
  have hstep := st157_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p168 : ((179412501321/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT157 (i+1))
      = (∑ i ∈ Finset.range 167, stT157 (i+1)) + stT157 168 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 167
    simpa using h
  have hprev := st157_p167
  have hstep := st157_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p169 : ((486426715407/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT157 (i+1))
      = (∑ i ∈ Finset.range 168, stT157 (i+1)) + stT157 169 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 168
    simpa using h
  have hprev := st157_p168
  have hstep := st157_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p170 : ((2519483490477/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT157 (i+1))
      = (∑ i ∈ Finset.range 169, stT157 (i+1)) + stT157 170 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 169
    simpa using h
  have hprev := st157_p169
  have hstep := st157_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p171 : ((2436702741657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT157 (i+1))
      = (∑ i ∈ Finset.range 170, stT157 (i+1)) + stT157 171 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 170
    simpa using h
  have hprev := st157_p170
  have hstep := st157_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p172 : ((4500324520851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT157 (i+1))
      = (∑ i ∈ Finset.range 171, stT157 (i+1)) + stT157 172 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 171
    simpa using h
  have hprev := st157_p171
  have hstep := st157_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p173 : ((4210184177531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT157 (i+1))
      = (∑ i ∈ Finset.range 172, stT157 (i+1)) + stT157 173 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 172
    simpa using h
  have hprev := st157_p172
  have hstep := st157_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p174 : ((4224060403323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT157 (i+1))
      = (∑ i ∈ Finset.range 173, stT157 (i+1)) + stT157 174 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 173
    simpa using h
  have hprev := st157_p173
  have hstep := st157_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p175 : ((4528461647967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT157 (i+1))
      = (∑ i ∈ Finset.range 174, stT157 (i+1)) + stT157 175 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 174
    simpa using h
  have hprev := st157_p174
  have hstep := st157_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p176 : ((2446323802111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT157 (i+1))
      = (∑ i ∈ Finset.range 175, stT157 (i+1)) + stT157 176 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 175
    simpa using h
  have hprev := st157_p175
  have hstep := st157_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p177 : ((252312435963/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT157 (i+1))
      = (∑ i ∈ Finset.range 176, stT157 (i+1)) + stT157 177 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 176
    simpa using h
  have hprev := st157_p176
  have hstep := st157_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p178 : ((2439353477799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT157 (i+1))
      = (∑ i ∈ Finset.range 177, stT157 (i+1)) + stT157 178 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 177
    simpa using h
  have hprev := st157_p177
  have hstep := st157_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p179 : ((45146267691/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT157 (i+1))
      = (∑ i ∈ Finset.range 178, stT157 (i+1)) + stT157 179 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 178
    simpa using h
  have hprev := st157_p178
  have hstep := st157_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p180 : ((2108605731939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT157 (i+1))
      = (∑ i ∈ Finset.range 179, stT157 (i+1)) + stT157 180 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 179
    simpa using h
  have hprev := st157_p179
  have hstep := st157_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p181 : ((524634450291/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT157 (i+1))
      = (∑ i ∈ Finset.range 180, stT157 (i+1)) + stT157 181 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 180
    simpa using h
  have hprev := st157_p180
  have hstep := st157_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p182 : ((8931425528583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT157 (i+1))
      = (∑ i ∈ Finset.range 181, stT157 (i+1)) + stT157 182 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 181
    simpa using h
  have hprev := st157_p181
  have hstep := st157_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p183 : ((2416723006281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT157 (i+1))
      = (∑ i ∈ Finset.range 182, stT157 (i+1)) + stT157 183 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 182
    simpa using h
  have hprev := st157_p182
  have hstep := st157_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p184 : ((10092117862369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT157 (i+1))
      = (∑ i ∈ Finset.range 183, stT157 (i+1)) + stT157 184 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 183
    simpa using h
  have hprev := st157_p183
  have hstep := st157_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p185 : ((4960058994597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT157 (i+1))
      = (∑ i ∈ Finset.range 184, stT157 (i+1)) + stT157 185 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 184
    simpa using h
  have hprev := st157_p184
  have hstep := st157_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p186 : ((185451153657/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT157 (i+1))
      = (∑ i ∈ Finset.range 185, stT157 (i+1)) + stT157 186 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 185
    simpa using h
  have hprev := st157_p185
  have hstep := st157_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p187 : ((343458362897/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT157 (i+1))
      = (∑ i ∈ Finset.range 186, stT157 (i+1)) + stT157 187 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 186
    simpa using h
  have hprev := st157_p186
  have hstep := st157_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p188 : ((2661089841/3200000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT157 (i+1))
      = (∑ i ∈ Finset.range 187, stT157 (i+1)) + stT157 188 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 187
    simpa using h
  have hprev := st157_p187
  have hstep := st157_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p189 : ((8634163029669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT157 (i+1))
      = (∑ i ∈ Finset.range 188, stT157 (i+1)) + stT157 189 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 188
    simpa using h
  have hprev := st157_p188
  have hstep := st157_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p190 : ((1865886912377/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT157 (i+1))
      = (∑ i ∈ Finset.range 189, stT157 (i+1)) + stT157 190 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 189
    simpa using h
  have hprev := st157_p189
  have hstep := st157_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p191 : ((9951956387767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT157 (i+1))
      = (∑ i ∈ Finset.range 190, stT157 (i+1)) + stT157 191 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 190
    simpa using h
  have hprev := st157_p190
  have hstep := st157_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p192 : ((1263342165043/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT157 (i+1))
      = (∑ i ∈ Finset.range 191, stT157 (i+1)) + stT157 192 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 191
    simpa using h
  have hprev := st157_p191
  have hstep := st157_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p193 : ((1212578761229/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT157 (i+1))
      = (∑ i ∈ Finset.range 192, stT157 (i+1)) + stT157 193 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 192
    simpa using h
  have hprev := st157_p192
  have hstep := st157_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p194 : ((8991809989943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT157 (i+1))
      = (∑ i ∈ Finset.range 193, stT157 (i+1)) + stT157 194 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 193
    simpa using h
  have hprev := st157_p193
  have hstep := st157_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p195 : ((8420459069423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT157 (i+1))
      = (∑ i ∈ Finset.range 194, stT157 (i+1)) + stT157 195 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 194
    simpa using h
  have hprev := st157_p194
  have hstep := st157_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p196 : ((8334514749331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT157 (i+1))
      = (∑ i ∈ Finset.range 195, stT157 (i+1)) + stT157 196 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 195
    simpa using h
  have hprev := st157_p195
  have hstep := st157_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p197 : ((8781601786321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT157 (i+1))
      = (∑ i ∈ Finset.range 196, stT157 (i+1)) + stT157 197 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 196
    simpa using h
  have hprev := st157_p196
  have hstep := st157_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p198 : ((2372216137451/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT157 (i+1))
      = (∑ i ∈ Finset.range 197, stT157 (i+1)) + stT157 198 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 197
    simpa using h
  have hprev := st157_p197
  have hstep := st157_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p199 : ((10033967810207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT157 (i+1))
      = (∑ i ∈ Finset.range 198, stT157 (i+1)) + stT157 199 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 198
    simpa using h
  have hprev := st157_p198
  have hstep := st157_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p200 : ((10097720487167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT157 (i+1))
      = (∑ i ∈ Finset.range 199, stT157 (i+1)) + stT157 200 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 199
    simpa using h
  have hprev := st157_p199
  have hstep := st157_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p201 : ((9647227987849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT157 (i+1))
      = (∑ i ∈ Finset.range 200, stT157 (i+1)) + stT157 201 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 200
    simpa using h
  have hprev := st157_p200
  have hstep := st157_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p202 : ((8947035402169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT157 (i+1))
      = (∑ i ∈ Finset.range 201, stT157 (i+1)) + stT157 202 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 201
    simpa using h
  have hprev := st157_p201
  have hstep := st157_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p203 : ((839965736151/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT157 (i+1))
      = (∑ i ∈ Finset.range 202, stT157 (i+1)) + stT157 203 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 202
    simpa using h
  have hprev := st157_p202
  have hstep := st157_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p204 : ((2078444866683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT157 (i+1))
      = (∑ i ∈ Finset.range 203, stT157 (i+1)) + stT157 204 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 203
    simpa using h
  have hprev := st157_p203
  have hstep := st157_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p205 : ((4366767599151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT157 (i+1))
      = (∑ i ∈ Finset.range 204, stT157 (i+1)) + stT157 205 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 204
    simpa using h
  have hprev := st157_p204
  have hstep := st157_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p206 : ((294409741663/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT157 (i+1))
      = (∑ i ∈ Finset.range 205, stT157 (i+1)) + stT157 206 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 205
    simpa using h
  have hprev := st157_p205
  have hstep := st157_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p207 : ((1249423958497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT157 (i+1))
      = (∑ i ∈ Finset.range 206, stT157 (i+1)) + stT157 207 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 206
    simpa using h
  have hprev := st157_p206
  have hstep := st157_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p208 : ((5071937575363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT157 (i+1))
      = (∑ i ∈ Finset.range 207, stT157 (i+1)) + stT157 208 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 207
    simpa using h
  have hprev := st157_p207
  have hstep := st157_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p209 : ((2447476650159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT157 (i+1))
      = (∑ i ∈ Finset.range 208, stT157 (i+1)) + stT157 209 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 208
    simpa using h
  have hprev := st157_p208
  have hstep := st157_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p210 : ((182549955117/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT157 (i+1))
      = (∑ i ∈ Finset.range 209, stT157 (i+1)) + stT157 210 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 209
    simpa using h
  have hprev := st157_p209
  have hstep := st157_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p211 : ((1702216374279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT157 (i+1))
      = (∑ i ∈ Finset.range 210, stT157 (i+1)) + stT157 211 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 210
    simpa using h
  have hprev := st157_p210
  have hstep := st157_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p212 : ((8264678932691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT157 (i+1))
      = (∑ i ∈ Finset.range 211, stT157 (i+1)) + stT157 212 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 211
    simpa using h
  have hprev := st157_p211
  have hstep := st157_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p213 : ((8513653640687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT157 (i+1))
      = (∑ i ∈ Finset.range 212, stT157 (i+1)) + stT157 213 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 212
    simpa using h
  have hprev := st157_p212
  have hstep := st157_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p214 : ((4562542096591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT157 (i+1))
      = (∑ i ∈ Finset.range 213, stT157 (i+1)) + stT157 214 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 213
    simpa using h
  have hprev := st157_p213
  have hstep := st157_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p215 : ((2445654619593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT157 (i+1))
      = (∑ i ∈ Finset.range 214, stT157 (i+1)) + stT157 215 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 214
    simpa using h
  have hprev := st157_p214
  have hstep := st157_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p216 : ((1015193712899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT157 (i+1))
      = (∑ i ∈ Finset.range 215, stT157 (i+1)) + stT157 216 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 215
    simpa using h
  have hprev := st157_p215
  have hstep := st157_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p217 : ((2009909523297/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT157 (i+1))
      = (∑ i ∈ Finset.range 216, stT157 (i+1)) + stT157 217 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 216
    simpa using h
  have hprev := st157_p216
  have hstep := st157_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p218 : ((381218076843/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT157 (i+1))
      = (∑ i ∈ Finset.range 217, stT157 (i+1)) + stT157 218 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 217
    simpa using h
  have hprev := st157_p217
  have hstep := st157_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p219 : ((8854828120797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT157 (i+1))
      = (∑ i ∈ Finset.range 218, stT157 (i+1)) + stT157 219 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 218
    simpa using h
  have hprev := st157_p218
  have hstep := st157_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p220 : ((8355195355797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT157 (i+1))
      = (∑ i ∈ Finset.range 219, stT157 (i+1)) + stT157 220 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 219
    simpa using h
  have hprev := st157_p219
  have hstep := st157_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p221 : ((8272919375821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT157 (i+1))
      = (∑ i ∈ Finset.range 220, stT157 (i+1)) + stT157 221 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 220
    simpa using h
  have hprev := st157_p220
  have hstep := st157_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p222 : ((1728836413837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT157 (i+1))
      = (∑ i ∈ Finset.range 221, stT157 (i+1)) + stT157 222 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 221
    simpa using h
  have hprev := st157_p221
  have hstep := st157_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p223 : ((453511343/488281250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT157 (i+1))
      = (∑ i ∈ Finset.range 222, stT157 (i+1)) + stT157 223 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 222
    simpa using h
  have hprev := st157_p222
  have hstep := st157_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p224 : ((9897001247593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT157 (i+1))
      = (∑ i ∈ Finset.range 223, stT157 (i+1)) + stT157 224 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 223
    simpa using h
  have hprev := st157_p223
  have hstep := st157_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p225 : ((2037141791777/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT157 (i+1))
      = (∑ i ∈ Finset.range 224, stT157 (i+1)) + stT157 225 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 224
    simpa using h
  have hprev := st157_p224
  have hstep := st157_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p226 : ((5011106164093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT157 (i+1))
      = (∑ i ∈ Finset.range 225, stT157 (i+1)) + stT157 226 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 225
    simpa using h
  have hprev := st157_p225
  have hstep := st157_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p227 : ((948561868687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT157 (i+1))
      = (∑ i ∈ Finset.range 226, stT157 (i+1)) + stT157 227 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 226
    simpa using h
  have hprev := st157_p226
  have hstep := st157_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p228 : ((1764908091227/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT157 (i+1))
      = (∑ i ∈ Finset.range 227, stT157 (i+1)) + stT157 228 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 227
    simpa using h
  have hprev := st157_p227
  have hstep := st157_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p229 : ((2085006826129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT157 (i+1))
      = (∑ i ∈ Finset.range 228, stT157 (i+1)) + stT157 229 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 228
    simpa using h
  have hprev := st157_p228
  have hstep := st157_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p230 : ((257772958947/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT157 (i+1))
      = (∑ i ∈ Finset.range 229, stT157 (i+1)) + stT157 230 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 229
    simpa using h
  have hprev := st157_p229
  have hstep := st157_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p231 : ((1717652875659/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT157 (i+1))
      = (∑ i ∈ Finset.range 230, stT157 (i+1)) + stT157 231 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 230
    simpa using h
  have hprev := st157_p230
  have hstep := st157_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p232 : ((9204883828419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT157 (i+1))
      = (∑ i ∈ Finset.range 231, stT157 (i+1)) + stT157 232 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 231
    simpa using h
  have hprev := st157_p231
  have hstep := st157_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p233 : ((9825690900681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT157 (i+1))
      = (∑ i ∈ Finset.range 232, stT157 (i+1)) + stT157 233 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 232
    simpa using h
  have hprev := st157_p232
  have hstep := st157_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p234 : ((10180338576721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT157 (i+1))
      = (∑ i ∈ Finset.range 233, stT157 (i+1)) + stT157 234 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 233
    simpa using h
  have hprev := st157_p233
  have hstep := st157_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p235 : ((10117756741777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT157 (i+1))
      = (∑ i ∈ Finset.range 234, stT157 (i+1)) + stT157 235 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 234
    simpa using h
  have hprev := st157_p234
  have hstep := st157_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p236 : ((9668000614817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT157 (i+1))
      = (∑ i ∈ Finset.range 235, stT157 (i+1)) + stT157 236 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 235
    simpa using h
  have hprev := st157_p235
  have hstep := st157_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p237 : ((9025144570337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT157 (i+1))
      = (∑ i ∈ Finset.range 236, stT157 (i+1)) + stT157 237 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 236
    simpa using h
  have hprev := st157_p236
  have hstep := st157_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p238 : ((8461559713313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT157 (i+1))
      = (∑ i ∈ Finset.range 237, stT157 (i+1)) + stT157 238 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 237
    simpa using h
  have hprev := st157_p237
  have hstep := st157_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p239 : ((8212189845261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT157 (i+1))
      = (∑ i ∈ Finset.range 238, stT157 (i+1)) + stT157 239 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 238
    simpa using h
  have hprev := st157_p238
  have hstep := st157_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p240 : ((4188996425089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT157 (i+1))
      = (∑ i ∈ Finset.range 239, stT157 (i+1)) + stT157 240 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 239
    simpa using h
  have hprev := st157_p239
  have hstep := st157_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p241 : ((4443781058159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT157 (i+1))
      = (∑ i ∈ Finset.range 240, stT157 (i+1)) + stT157 241 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 240
    simpa using h
  have hprev := st157_p240
  have hstep := st157_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p242 : ((38121333619/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT157 (i+1))
      = (∑ i ∈ Finset.range 241, stT157 (i+1)) + stT157 242 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 241
    simpa using h
  have hprev := st157_p241
  have hstep := st157_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p243 : ((40180363867/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT157 (i+1))
      = (∑ i ∈ Finset.range 242, stT157 (i+1)) + stT157 243 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 242
    simpa using h
  have hprev := st157_p242
  have hstep := st157_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p244 : ((5113038052511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT157 (i+1))
      = (∑ i ∈ Finset.range 243, stT157 (i+1)) + stT157 244 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 243
    simpa using h
  have hprev := st157_p243
  have hstep := st157_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p245 : ((500185237157/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT157 (i+1))
      = (∑ i ∈ Finset.range 244, stT157 (i+1)) + stT157 245 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 244
    simpa using h
  have hprev := st157_p244
  have hstep := st157_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p246 : ((9468909618579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT157 (i+1))
      = (∑ i ∈ Finset.range 245, stT157 (i+1)) + stT157 246 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 245
    simpa using h
  have hprev := st157_p245
  have hstep := st157_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p247 : ((4416889737927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT157 (i+1))
      = (∑ i ∈ Finset.range 246, stT157 (i+1)) + stT157 247 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 246
    simpa using h
  have hprev := st157_p246
  have hstep := st157_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p248 : ((2086552299507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT157 (i+1))
      = (∑ i ∈ Finset.range 247, stT157 (i+1)) + stT157 248 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 247
    simpa using h
  have hprev := st157_p247
  have hstep := st157_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p249 : ((8193337617453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT157 (i+1))
      = (∑ i ∈ Finset.range 248, stT157 (i+1)) + stT157 249 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 248
    simpa using h
  have hprev := st157_p248
  have hstep := st157_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_p250 : ((4215618099079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT157 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT157 (i+1))
      = (∑ i ∈ Finset.range 249, stT157 (i+1)) + stT157 250 := by
    have h := Finset.sum_range_succ (fun i => stT157 (i+1)) 249
    simpa using h
  have hprev := st157_p249
  have hstep := st157_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st157_s250 :
    |Real.sin (((157 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((9749/10000 : ℚ) : ℝ))
      - ((-463269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1481379/5000000) (δ := 1973/250000000) (ψ := 9749/10000) 157 138
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 157`** (evaluated boundary). -/
theorem station_157_sign : hardyG ((((157:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 157 250 (by norm_num) (by norm_num)
    ((9749/10000 : ℚ) : ℝ)
  have hchain := st157_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT157 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((157 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((9749/10000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st157_c250
  have hsinb := abs_le.mp st157_s250
  have hbdy_lo : ((36750819227671/394388000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((157 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((9749/10000 : ℚ) : ℝ))) / 2
          - ((((157:ℕ)):ℝ))
            * Real.sin (((157 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((9749/10000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((157:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((157:ℝ) * Real.log (250:ℝ) - ((9749/10000 : ℚ) : ℝ))) / 2
        - ((157:ℝ)) * Real.sin ((157:ℝ) * Real.log (250:ℝ) - ((9749/10000 : ℚ) : ℝ))
        ≥ ((290540981/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((157:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((290540981/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((290540981/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((290540981/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((157:ℕ)):ℝ))+1) * (((((157:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((176380989477/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((4215618099079/5000000000000 : ℚ) : ℝ) + ((36750819227671/394388000000000 : ℚ) : ℝ)
      - ((176380989477/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((9749/10000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((157:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((9749/10000 : ℚ) : ℝ)
        * (riemannZeta (line ((((157:ℕ)):ℝ)))).re
      - Real.sin ((9749/10000 : ℚ) : ℝ)
        * (riemannZeta (line ((((157:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((157:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((157:ℕ)):ℝ))
      = (((((157:ℕ)):ℝ)) * (Real.log ((((157:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((157:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_157
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
  have hθwin : |(((9749/10000 : ℚ) : ℝ) + ((28:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((157:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((157:ℕ)):ℝ)))
    (φ := ((9749/10000 : ℚ) : ℝ) + ((28:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((9749/10000 : ℚ) : ℝ) + ((28:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((9749/10000 : ℚ)) : ℝ) - Real.pi) + ((28:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((9749/10000 : ℚ)) : ℝ) - Real.pi) 28).1,
    (cos_sin_shift ((((9749/10000 : ℚ)) : ℝ) - Real.pi) 28).2]
  exact cos_sin_flip ((9749/10000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_157_sign
end AxiomAudit
