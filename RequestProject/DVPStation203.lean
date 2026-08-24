import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 203` (rung-217.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT203 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((203 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))

theorem st203_c1 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((447809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 576221/5000000) (δ := 201/1000000000) (ψ := -460977/1000000) 203 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t1 : ((55973/62500 : ℚ) : ℝ) ≤ stT203 1 := by
  have hc : ((55973/62500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55973/62500 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((55973/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c2 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-979703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7349429/10000000) (δ := 2561/250000000) (ψ := -460977/1000000) 203 22
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t2 : ((-1731975021551/2500000000000 : ℚ) : ℝ) ≤ stT203 2 := by
  have hc : ((-979753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1731975021551/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-979753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c3 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-910549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3394259/5000000) (δ := 513/50000000) (ψ := -460977/1000000) 203 36
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t3 : ((-5257346058297/10000000000000 : ℚ) : ℝ) ≤ stT203 3 := by
  have hc : ((-910599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5257346058297/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-910599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c4 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((324469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1080761/5000000) (δ := 5089/500000000) (ψ := -460977/1000000) 203 45
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t4 : ((81111/250000 : ℚ) : ℝ) ≤ stT203 4 := by
  have hc : ((81111/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81111/250000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((81111/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c5 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((179981/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70507/625000) (δ := 2557/250000000) (ψ := -460977/1000000) 203 52
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t5 : ((160970921617/400000000000 : ℚ) : ℝ) ≤ stT203 5 := by
  have hc : ((179971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160970921617/400000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((179971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c6 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((48607/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295753/5000000) (δ := 5109/500000000) (ψ := -460977/1000000) 203 58
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t6 : ((198426996369/500000000000 : ℚ) : ℝ) ≤ stT203 6 := by
  have hc : ((97209/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198426996369/500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((97209/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c7 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((935919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449921/5000000) (δ := 5127/500000000) (ψ := -460977/1000000) 203 63
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t7 : ((884312912659/2500000000000 : ℚ) : ℝ) ≤ stT203 7 := by
  have hc : ((935869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((884312912659/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((935869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c8 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-21693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403549/1000000) (δ := 511/50000000) (ψ := -460977/1000000) 203 67
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t8 : ((-19196181853/1250000000000 : ℚ) : ℝ) ≤ stT203 8 := by
  have hc : ((-10859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19196181853/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-10859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c9 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((462187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97851/1000000) (δ := 10311/1000000000) (ψ := -460977/1000000) 203 71
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t9 : ((770269922973/2500000000000 : ℚ) : ℝ) ≤ stT203 9 := by
  have hc : ((231081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((770269922973/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((231081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c10 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-122213/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3662537/5000000) (δ := 10333/1000000000) (ψ := -460977/1000000) 203 74
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t10 : ((-772982490903/2500000000000 : ℚ) : ℝ) ≤ stT203 10 := by
  have hc : ((-488877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772982490903/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-488877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c11 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-959139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7136853/10000000) (δ := 5081/500000000) (ψ := -460977/1000000) 203 78
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t11 : ((-1446032091273/5000000000000 : ℚ) : ℝ) ≤ stT203 11 := by
  have hc : ((-959189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1446032091273/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-959189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c12 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-622087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2802753/5000000) (δ := 159/15625000) (ψ := -460977/1000000) 203 80
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t12 : ((-56123600907/312500000000 : ℚ) : ℝ) ≤ stT203 12 := by
  have hc : ((-622137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56123600907/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-622137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c13 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((936359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -448357/5000000) (δ := 5153/500000000) (ψ := -460977/1000000) 203 83
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t13 : ((5193706023/20000000000 : ℚ) : ℝ) ≤ stT203 13 := by
  have hc : ((936309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5193706023/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((936309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c14 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-260521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529717/1000000) (δ := 2553/250000000) (ψ := -460977/1000000) 203 85
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t14 : ((-348169313349/2500000000000 : ℚ) : ℝ) ≤ stT203 14 := by
  have hc : ((-130273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348169313349/2500000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-130273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c15 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-36581/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6812823/10000000) (δ := 10233/1000000000) (ψ := -460977/1000000) 203 88
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t15 : ((-94456903587/400000000000 : ℚ) : ℝ) ≤ stT203 15 := by
  have hc : ((-36583/40000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94456903587/400000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-36583/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c16 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-580537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5475461/10000000) (δ := 2031/200000000) (ψ := -460977/1000000) 203 90
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t16 : ((-1451468080587/10000000000000 : ℚ) : ℝ) ≤ stT203 16 := by
  have hc : ((-580587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1451468080587/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-580587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c17 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-770079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6124403/10000000) (δ := 5081/500000000) (ψ := -460977/1000000) 203 92
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t17 : ((-1867837761053/10000000000000 : ℚ) : ℝ) ≤ stT203 17 := by
  have hc : ((-770129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1867837761053/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-770129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c18 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-963401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3587761/5000000) (δ := 10269/1000000000) (ψ := -460977/1000000) 203 93
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t18 : ((-2270876166373/10000000000000 : ℚ) : ℝ) ≤ stT203 18 := by
  have hc : ((-963451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2270876166373/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-963451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c19 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((143607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3198699/10000000) (δ := 10219/1000000000) (ψ := -460977/1000000) 203 95
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t19 : ((164699825187/2500000000000 : ℚ) : ℝ) ≤ stT203 19 := by
  have hc : ((71791/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164699825187/2500000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((71791/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c20 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((128299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1092939/5000000) (δ := 2061/200000000) (ψ := -460977/1000000) 203 97
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t20 : ((286862799363/2000000000000 : ℚ) : ℝ) ≤ stT203 20 := by
  have hc : ((128289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286862799363/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((128289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c21 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-184621/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3433593/5000000) (δ := 2061/200000000) (ψ := -460977/1000000) 203 98
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t21 : ((-402897890949/2000000000000 : ℚ) : ℝ) ≤ stT203 21 := by
  have hc : ((-184631/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402897890949/2000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-184631/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c22 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((232541/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -939841/10000000) (δ := 1273/125000000) (ψ := -460977/1000000) 203 100
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t22 : ((991504779399/5000000000000 : ℚ) : ℝ) ≤ stT203 22 := by
  have hc : ((465057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((991504779399/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((465057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c23 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-713021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1477871/2500000) (δ := 2569/250000000) (ψ := -460977/1000000) 203 101
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t23 : ((-297371286059/2000000000000 : ℚ) : ℝ) ≤ stT203 23 := by
  have hc : ((-713071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297371286059/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-713071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c24 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((4309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781089/2000000) (δ := 10241/1000000000) (ψ := -460977/1000000) 203 103
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t24 : ((2186169111/1250000000000 : ℚ) : ℝ) ≤ stT203 24 := by
  have hc : ((1071/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2186169111/1250000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((1071/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c25 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((904111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1103757/10000000) (δ := 2587/250000000) (ψ := -460977/1000000) 203 104
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t25 : ((904061/5000000 : ℚ) : ℝ) ≤ stT203 25 := by
  have hc : ((904061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((904061/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((904061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c26 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-52211/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2650149/5000000) (δ := 2587/250000000) (ψ := -460977/1000000) 203 105
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t26 : ((-6400252187/62500000000 : ℚ) : ℝ) ≤ stT203 26 := by
  have hc : ((-6527/12500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6400252187/62500000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-6527/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c27 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-937081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3481213/5000000) (δ := 10233/1000000000) (ψ := -460977/1000000) 203 107
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t27 : ((-1803509546631/10000000000000 : ℚ) : ℝ) ≤ stT203 27 := by
  have hc : ((-937131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1803509546631/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-937131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c28 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-22893/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4213781/10000000) (δ := 10277/1000000000) (ψ := -460977/1000000) 203 108
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t28 : ((-43282616169/2000000000000 : ℚ) : ℝ) ≤ stT203 28 := by
  have hc : ((-22903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43282616169/2000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-22903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c29 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((663609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211291/1000000) (δ := 10219/1000000000) (ψ := -460977/1000000) 203 109
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t29 : ((1232197875727/10000000000000 : ℚ) : ℝ) ≤ stT203 29 := by
  have hc : ((663559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1232197875727/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((663559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c30 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((96981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -307931/5000000) (δ := 2553/250000000) (ψ := -460977/1000000) 203 110
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t30 : ((11065816201/62500000000 : ℚ) : ℝ) ≤ stT203 30 := by
  have hc : ((6061/6250 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11065816201/62500000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((6061/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c31 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((991969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317049/10000000) (δ := 2041/200000000) (ψ := -460977/1000000) 203 111
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t31 : ((1781539095707/10000000000000 : ℚ) : ℝ) ≤ stT203 31 := by
  have hc : ((991919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1781539095707/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((991919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c32 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((958637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 721551/10000000) (δ := 10197/1000000000) (ψ := -460977/1000000) 203 112
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t32 : ((847278753321/5000000000000 : ℚ) : ℝ) ≤ stT203 32 := by
  have hc : ((958587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((847278753321/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((958587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c33 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((484199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25207/400000) (δ := 10213/1000000000) (ψ := -460977/1000000) 203 113
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t33 : ((52677404939/312500000000 : ℚ) : ℝ) ≤ stT203 33 := by
  have hc : ((242087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52677404939/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((242087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c34 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((499789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72609/10000000) (δ := 10183/1000000000) (ψ := -460977/1000000) 203 114
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t34 : ((42854388177/250000000000 : ℚ) : ℝ) ≤ stT203 34 := by
  have hc : ((124941/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42854388177/250000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((124941/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c35 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((932443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462099/5000000) (δ := 159/15625000) (ψ := -460977/1000000) 203 115
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t35 : ((394007836761/2500000000000 : ℚ) : ℝ) ≤ stT203 35 := by
  have hc : ((932393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((394007836761/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((932393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c36 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((118897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2335429/10000000) (δ := 5167/500000000) (ψ := -460977/1000000) 203 116
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t36 : ((99072460371/1000000000000 : ℚ) : ℝ) ≤ stT203 36 := by
  have hc : ((118887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99072460371/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((118887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c37 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-84463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5173/12500) (δ := 5121/500000000) (ψ := -460977/1000000) 203 117
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t37 : ((-13893852687/1000000000000 : ℚ) : ℝ) ≤ stT203 37 := by
  have hc : ((-84513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13893852687/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-84513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c38 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-203949/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1578063/2500000) (δ := 5077/500000000) (ψ := -460977/1000000) 203 118
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t38 : ((-132347761889/1000000000000 : ℚ) : ℝ) ≤ stT203 38 := by
  have hc : ((-407923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132347761889/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-407923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c39 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-184717/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3435157/5000000) (δ := 5127/500000000) (ψ := -460977/1000000) 203 118
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t39 : ((-147900010007/1000000000000 : ℚ) : ℝ) ≤ stT203 39 := by
  have hc : ((-184727/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147900010007/1000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-184727/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c40 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-33651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2005567/5000000) (δ := 10347/1000000000) (ψ := -460977/1000000) 203 119
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t40 : ((-53285965439/10000000000000 : ℚ) : ℝ) ≤ stT203 40 := by
  have hc : ((-33701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53285965439/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-33701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c41 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((472391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 417333/5000000) (δ := 10263/1000000000) (ψ := -460977/1000000) 203 120
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t41 : ((368855729871/2500000000000 : ℚ) : ℝ) ≤ stT203 41 := by
  have hc : ((236183/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368855729871/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((236183/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c42 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((245523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1321883/5000000) (δ := 10333/1000000000) (ψ := -460977/1000000) 203 121
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t42 : ((189405757717/2500000000000 : ℚ) : ℝ) ≤ stT203 42 := by
  have hc : ((122749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189405757717/2500000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((122749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c43 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-41889/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641/1000) (δ := 10177/1000000000) (ψ := -460977/1000000) 203 122
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t43 : ((-63883951019/500000000000 : ℚ) : ℝ) ≤ stT203 43 := by
  have hc : ((-83783/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63883951019/500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-83783/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c44 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-12683/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5257171/10000000) (δ := 5113/500000000) (ψ := -460977/1000000) 203 122
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t44 : ((-76488919509/1000000000000 : ℚ) : ℝ) ≤ stT203 44 := by
  have hc : ((-50737/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76488919509/1000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-50737/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c45 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((928047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 477077/5000000) (δ := 2037/200000000) (ψ := -460977/1000000) 203 123
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t45 : ((1383375335867/10000000000000 : ℚ) : ℝ) ≤ stT203 45 := by
  have hc : ((927997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1383375335867/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((927997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c46 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((26123/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1799759/5000000) (δ := 10311/1000000000) (ψ := -460977/1000000) 203 124
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t46 : ((38501503347/2000000000000 : ℚ) : ℝ) ≤ stT203 46 := by
  have hc : ((26113/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38501503347/2000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((26113/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c47 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-244211/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731493/1000000) (δ := 2573/250000000) (ψ := -460977/1000000) 203 124
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t47 : ((-14249464331/100000000000 : ℚ) : ℝ) ≤ stT203 47 := by
  have hc : ((-488447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14249464331/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-488447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c48 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((1217/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2291567/10000000) (δ := 10199/1000000000) (ψ := -460977/1000000) 203 125
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t48 : ((140515443/1600000000 : ℚ) : ℝ) ≤ stT203 48 := by
  have hc : ((12169/20000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140515443/1600000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((12169/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c49 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((380129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -369019/1250000) (δ := 5153/500000000) (ψ := -460977/1000000) 203 126
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t49 : ((542969837109/10000000000000 : ℚ) : ℝ) ≤ stT203 49 := by
  have hc : ((380079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((542969837109/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((380079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c50 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-15244/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7300769/10000000) (δ := 5153/500000000) (ψ := -460977/1000000) 203 126
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t50 : ((-344950129131/2500000000000 : ℚ) : ℝ) ≤ stT203 50 := by
  have hc : ((-487833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344950129131/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-487833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c51 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((791797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13141/80000) (δ := 10213/1000000000) (ψ := -460977/1000000) 203 127
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t51 : ((27716687229/250000000000 : ℚ) : ℝ) ≤ stT203 51 := by
  have hc : ((791747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27716687229/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((791747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c52 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-56611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4210653/10000000) (δ := 10283/1000000000) (ψ := -460977/1000000) 203 128
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t52 : ((-19635007409/1250000000000 : ℚ) : ℝ) ≤ stT203 52 := by
  have hc : ((-14159/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19635007409/1250000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-14159/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c53 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-287141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5456309/10000000) (δ := 511/50000000) (ψ := -460977/1000000) 203 128
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t53 : ((-98613235149/1250000000000 : ℚ) : ℝ) ≤ stT203 53 := by
  have hc : ((-143583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98613235149/1250000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-143583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c54 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((119187/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382707/5000000) (δ := 411/40000000) (ψ := -460977/1000000) 203 129
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t54 : ((648737529921/5000000000000 : ℚ) : ℝ) ≤ stT203 54 := by
  have hc : ((476723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((648737529921/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((476723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c55 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-19237/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7161209/10000000) (δ := 2567/250000000) (ψ := -460977/1000000) 203 130
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t55 : ((-32425649/250000000 : ℚ) : ℝ) ≤ stT203 55 := by
  have hc : ((-9619/10000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32425649/250000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-9619/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c56 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((701517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99159/500000) (δ := 1271/125000000) (ψ := -460977/1000000) 203 130
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t56 : ((468687280451/5000000000000 : ℚ) : ℝ) ≤ stT203 56 := by
  have hc : ((701467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468687280451/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((701467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c57 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-320349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1185559/2500000) (δ := 5121/500000000) (ψ := -460977/1000000) 203 131
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t57 : ((-424379048667/10000000000000 : ℚ) : ℝ) ≤ stT203 57 := by
  have hc : ((-320399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424379048667/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-320399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c58 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-62803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2042051/5000000) (δ := 10261/1000000000) (ψ := -460977/1000000) 203 131
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t58 : ((-16506014889/2000000000000 : ℚ) : ℝ) ≤ stT203 58 := by
  have hc : ((-62853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16506014889/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-62853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c59 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((381497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2948453/10000000) (δ := 5077/500000000) (ψ := -460977/1000000) 203 132
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t59 : ((496601653383/10000000000000 : ℚ) : ℝ) ≤ stT203 59 := by
  have hc : ((381447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496601653383/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((381447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c60 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-61443/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 111623/200000) (δ := 5127/500000000) (ψ := -460977/1000000) 203 132
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t60 : ((-1983226519/25000000000 : ℚ) : ℝ) ≤ stT203 60 := by
  have hc : ((-7681/12500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1983226519/25000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-7681/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c61 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((191969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1738193/10000000) (δ := 641/62500000) (ψ := -460977/1000000) 203 133
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t61 : ((30721869999/312500000000 : ℚ) : ℝ) ≤ stT203 61 := by
  have hc : ((383913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30721869999/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((383913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c62 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-214941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651401/1000000) (δ := 10347/1000000000) (ψ := -460977/1000000) 203 133
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t62 : ((-272991374907/2500000000000 : ℚ) : ℝ) ≤ stT203 62 := by
  have hc : ((-429907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272991374907/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-429907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c63 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((454587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -859/8000) (δ := 10239/1000000000) (ψ := -460977/1000000) 203 134
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t63 : ((286347013561/2500000000000 : ℚ) : ℝ) ≤ stT203 63 := by
  have hc : ((227281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286347013561/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((227281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c64 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-186161/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432407/625000) (δ := 10339/1000000000) (ψ := -460977/1000000) 203 134
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t64 : ((-232713936171/2000000000000 : ℚ) : ℝ) ≤ stT203 64 := by
  have hc : ((-186171/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232713936171/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-186171/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c65 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((186579/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -921069/10000000) (δ := 10271/1000000000) (ψ := -460977/1000000) 203 135
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t65 : ((231410299443/2000000000000 : ℚ) : ℝ) ≤ stT203 65 := by
  have hc : ((186569/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231410299443/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((186569/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c66 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-458417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6827187/10000000) (δ := 10171/1000000000) (ψ := -460977/1000000) 203 135
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t66 : ((-56430313443/500000000000 : ℚ) : ℝ) ≤ stT203 66 := by
  have hc : ((-229221/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56430313443/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-229221/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c67 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((438883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -624521/5000000) (δ := 5089/500000000) (ψ := -460977/1000000) 203 136
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t67 : ((134037546363/1250000000000 : ℚ) : ℝ) ≤ stT203 67 := by
  have hc : ((219429/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134037546363/1250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((219429/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c68 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-100727/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6269621/10000000) (δ := 409/40000000) (ψ := -460977/1000000) 203 136
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t68 : ((-488628387507/5000000000000 : ℚ) : ℝ) ≤ stT203 68 := by
  have hc : ((-402933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-488628387507/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-402933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c69 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((43013/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2029451/10000000) (δ := 2037/200000000) (ψ := -460977/1000000) 203 137
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t69 : ((207111128391/2500000000000 : ℚ) : ℝ) ≤ stT203 69 := by
  have hc : ((344079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207111128391/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((344079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c70 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-256351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2636407/5000000) (δ := 5109/500000000) (ψ := -460977/1000000) 203 137
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t70 : ((-38303503763/625000000000 : ℚ) : ℝ) ≤ stT203 70 := by
  have hc : ((-32047/62500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38303503763/625000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-32047/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c71 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((34089/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -647293/2000000) (δ := 10311/1000000000) (ψ := -460977/1000000) 203 138
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t71 : ((161795040511/5000000000000 : ℚ) : ℝ) ≤ stT203 71 := by
  have hc : ((136331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161795040511/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((136331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c72 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((327/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3861583/10000000) (δ := 2573/250000000) (ψ := -460977/1000000) 203 138
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t72 : ((3077092221/1000000000000 : ℚ) : ℝ) ≤ stT203 72 := by
  have hc : ((2611/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3077092221/1000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((2611/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c73 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-71897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4846281/10000000) (δ := 2551/250000000) (ψ := -460977/1000000) 203 139
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t73 : ((-21040203921/500000000000 : ℚ) : ℝ) ≤ stT203 73 := by
  have hc : ((-71907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21040203921/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-71907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c74 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((679713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2058561/10000000) (δ := 2551/250000000) (ψ := -460977/1000000) 203 139
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t74 : ((197522981397/2500000000000 : ℚ) : ℝ) ≤ stT203 74 := by
  have hc : ((679663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197522981397/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((679663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c75 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-918423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6837179/10000000) (δ := 2549/250000000) (ψ := -460977/1000000) 203 140
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t75 : ((-1060561691573/10000000000000 : ℚ) : ℝ) ≤ stT203 75 := by
  have hc : ((-918473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1060561691573/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-918473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c76 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((499469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2881/250000) (δ := 2549/250000000) (ψ := -460977/1000000) 203 140
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t76 : ((71612653079/625000000000 : ℚ) : ℝ) ≤ stT203 76 := by
  have hc : ((124861/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71612653079/625000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((124861/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c77 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-860751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6518851/10000000) (δ := 10207/1000000000) (ψ := -460977/1000000) 203 140
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t77 : ((-490486992203/5000000000000 : ℚ) : ℝ) ≤ stT203 77 := by
  have hc : ((-860801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490486992203/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-860801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c78 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((61517/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2640637/10000000) (δ := 10189/1000000000) (ψ := -460977/1000000) 203 141
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t78 : ((278588829911/5000000000000 : ℚ) : ℝ) ≤ stT203 78 := by
  have hc : ((246043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278588829911/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((246043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c79 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((20511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1912203/5000000) (δ := 5157/500000000) (ψ := -460977/1000000) 203 141
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t79 : ((11524266141/2500000000000 : ℚ) : ℝ) ≤ stT203 79 := by
  have hc : ((10243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11524266141/2500000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((10243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c80 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-294221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5499817/10000000) (δ := 5141/500000000) (ψ := -460977/1000000) 203 142
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t80 : ((-82244258091/1250000000000 : ℚ) : ℝ) ≤ stT203 80 := by
  have hc : ((-147123/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82244258091/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-147123/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c81 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((189731/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 402301/5000000) (δ := 5091/500000000) (ψ := -460977/1000000) 203 142
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t81 : ((210801090031/2000000000000 : ℚ) : ℝ) ≤ stT203 81 := by
  have hc : ((189721/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210801090031/2000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((189721/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c82 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-946391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3515839/5000000) (δ := 10221/1000000000) (ψ := -460977/1000000) 203 142
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t82 : ((-261292484839/2500000000000 : ℚ) : ℝ) ≤ stT203 82 := by
  have hc : ((-946441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261292484839/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-946441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c83 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((531971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100987/400000) (δ := 407/40000000) (ψ := -460977/1000000) 203 143
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t83 : ((291929415141/5000000000000 : ℚ) : ℝ) ≤ stT203 83 := by
  have hc : ((531921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291929415141/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((531921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c84 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((18619/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3553221/10000000) (δ := 163/8000000) (ψ := -460977/1000000) 203 143
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t84 : ((81232667139/5000000000000 : ℚ) : ℝ) ≤ stT203 84 := by
  have hc : ((74451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81232667139/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((74451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c85 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-776257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6148759/10000000) (δ := 2567/250000000) (ψ := -460977/1000000) 203 144
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t85 : ((-842023716471/10000000000000 : ℚ) : ℝ) ≤ stT203 85 := by
  have hc : ((-776307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-842023716471/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-776307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c86 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((996371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213039/10000000) (δ := 2567/250000000) (ψ := -460977/1000000) 203 144
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t86 : ((1074359834967/10000000000000 : ℚ) : ℝ) ≤ stT203 86 := by
  have hc : ((996321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1074359834967/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((996321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c87 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-637193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2827059/5000000) (δ := 1271/125000000) (ψ := -460977/1000000) 203 144
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t87 : ((-683196504459/10000000000000 : ℚ) : ℝ) ≤ stT203 87 := by
  have hc : ((-637243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-683196504459/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-637243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c88 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-16293/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212689/500000) (δ := 127/12500000) (ψ := -460977/1000000) 203 145
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t88 : ((-17375065697/1250000000000 : ℚ) : ℝ) ≤ stT203 88 := by
  have hc : ((-65197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17375065697/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-65197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c89 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((414833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370179/2500000) (δ := 513/50000000) (ψ := -460977/1000000) 203 145
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t89 : ((54961904447/625000000000 : ℚ) : ℝ) ≤ stT203 89 := by
  have hc : ((51851/62500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54961904447/625000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((51851/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c90 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-120093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3575583/5000000) (δ := 127/12500000) (ψ := -460977/1000000) 203 145
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t90 : ((-506383114921/5000000000000 : ℚ) : ℝ) ≤ stT203 90 := by
  have hc : ((-480397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-506383114921/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-480397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c91 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((76259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1474499/5000000) (δ := 409/20000000) (ψ := -460977/1000000) 203 146
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t91 : ((19982651679/500000000000 : ℚ) : ℝ) ≤ stT203 91 := by
  have hc : ((76249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19982651679/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((76249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c92 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((126771/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519499/2000000) (δ := 207/20000000) (ψ := -460977/1000000) 203 146
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t92 : ((66077431431/1250000000000 : ℚ) : ℝ) ≤ stT203 92 := by
  have hc : ((253517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66077431431/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((253517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c93 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-995769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7623937/10000000) (δ := 10157/1000000000) (ψ := -460977/1000000) 203 147
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t93 : ((-129077062961/1250000000000 : ℚ) : ℝ) ≤ stT203 93 := by
  have hc : ((-995819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129077062961/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-995819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c94 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((638361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274509/1250000) (δ := 10257/1000000000) (ψ := -460977/1000000) 203 147
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t94 : ((658367369931/10000000000000 : ℚ) : ℝ) ≤ stT203 94 := by
  have hc : ((638311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((658367369931/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((638311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c95 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((74133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3174343/10000000) (δ := 5173/500000000) (ψ := -460977/1000000) 203 147
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t95 : ((76046002349/2500000000000 : ℚ) : ℝ) ≤ stT203 95 := by
  have hc : ((148241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76046002349/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((148241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c96 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-967961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1443887/2000000) (δ := 2541/250000000) (ψ := -460977/1000000) 203 148
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t96 : ((-987972354831/10000000000000 : ℚ) : ℝ) ≤ stT203 96 := by
  have hc : ((-968011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-987972354831/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-968011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c97 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((354003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -980157/5000000) (δ := 2541/250000000) (ψ := -460977/1000000) 203 148
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t97 : ((89852536597/1250000000000 : ℚ) : ℝ) ≤ stT203 97 := by
  have hc : ((176989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89852536597/1250000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((176989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c98 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((269479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162243/500000) (δ := 1283/125000000) (ψ := -460977/1000000) 203 148
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t98 : ((34020530401/1250000000000 : ℚ) : ℝ) ≤ stT203 98 := by
  have hc : ((269429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34020530401/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((269429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c99 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-488243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7310761/10000000) (δ := 2583/250000000) (ψ := -460977/1000000) 203 149
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t99 : ((-61340986773/625000000000 : ℚ) : ℝ) ≤ stT203 99 := by
  have hc : ((-122067/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61340986773/625000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-122067/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c100 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((633991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2210233/10000000) (δ := 10271/1000000000) (ψ := -460977/1000000) 203 149
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t100 : ((633940366059/10000000000000 : ℚ) : ℝ) ≤ stT203 100 := by
  have hc : ((633941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633940366059/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((633941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c101 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((421373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 567919/2000000) (δ := 10271/1000000000) (ψ := -460977/1000000) 203 149
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t101 : ((419231973951/10000000000000 : ℚ) : ℝ) ≤ stT203 101 := by
  have hc : ((421323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419231973951/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((421323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c102 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-62499/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7839637/10000000) (δ := 10171/1000000000) (ψ := -460977/1000000) 203 149
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t102 : ((-123772708129/1250000000000 : ℚ) : ℝ) ≤ stT203 102 := by
  have hc : ((-500017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123772708129/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-500017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c103 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((393057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1458553/5000000) (δ := 413/40000000) (ψ := -460977/1000000) 203 150
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t103 : ((387241194303/10000000000000 : ℚ) : ℝ) ≤ stT203 103 := by
  have hc : ((393007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387241194303/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((393007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c104 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((1121/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1986309/10000000) (δ := 5139/500000000) (ψ := -460977/1000000) 203 150
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t104 : ((1373939667/20000000000 : ℚ) : ℝ) ≤ stT203 104 := by
  have hc : ((28023/40000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1373939667/20000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((28023/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c105 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-183863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 684283/1000000) (δ := 5089/500000000) (ψ := -460977/1000000) 203 150
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t105 : ((-179441844573/2000000000000 : ℚ) : ℝ) ≤ stT203 105 := by
  have hc : ((-183873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179441844573/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-183873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c106 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-51059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4054693/10000000) (δ := 5093/500000000) (ψ := -460977/1000000) 203 151
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t106 : ((-24820728087/5000000000000 : ℚ) : ℝ) ≤ stT203 106 := by
  have hc : ((-51109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24820728087/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-51109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c107 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((14998/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71063/1000000) (δ := 10317/1000000000) (ψ := -460977/1000000) 203 151
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t107 : ((28996702531/312500000000 : ℚ) : ℝ) ≤ stT203 107 := by
  have hc : ((479911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28996702531/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((479911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c108 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-566163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2715799/5000000) (δ := 10317/1000000000) (ψ := -460977/1000000) 203 151
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t108 : ((-544839025463/10000000000000 : ℚ) : ℝ) ≤ stT203 108 := by
  have hc : ((-566213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-544839025463/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-566213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c109 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-620029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279947/500000) (δ := 10293/1000000000) (ψ := -460977/1000000) 203 152
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t109 : ((-593928408333/10000000000000 : ℚ) : ℝ) ≤ stT203 109 := by
  have hc : ((-620079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-593928408333/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-620079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c110 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((926543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -964197/10000000) (δ := 1031/100000000) (ψ := -460977/1000000) 203 152
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t110 : ((441687934383/5000000000000 : ℚ) : ℝ) ≤ stT203 110 := by
  have hc : ((926493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441687934383/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((926493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c111 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((59531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 907157/2500000) (δ := 10293/1000000000) (ψ := -460977/1000000) 203 152
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t111 : ((28240268221/2500000000000 : ℚ) : ℝ) ≤ stT203 111 := by
  have hc : ((29753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28240268221/2500000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((29753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c112 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-991499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7527771/10000000) (δ := 51/5000000) (ψ := -460977/1000000) 203 153
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t112 : ((-58557909293/625000000000 : ℚ) : ℝ) ≤ stT203 112 := by
  have hc : ((-991549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58557909293/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-991549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c113 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((1113/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -754151/2500000) (δ := 10303/1000000000) (ψ := -460977/1000000) 203 153
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t113 : ((418749749/12500000000 : ℚ) : ℝ) ≤ stT203 113 := by
  have hc : ((35611/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418749749/12500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((35611/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c114 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((417707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181847/1250000) (δ := 51/5000000) (ψ := -460977/1000000) 203 153
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t114 : ((39119469597/500000000000 : ℚ) : ℝ) ≤ stT203 114 := by
  have hc : ((208841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39119469597/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((208841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c115 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-706157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5887129/10000000) (δ := 103/10000000) (ψ := -460977/1000000) 203 153
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t115 : ((-131708311707/2000000000000 : ℚ) : ℝ) ≤ stT203 115 := by
  have hc : ((-706207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131708311707/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-706207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c116 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-141153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54269/100000) (δ := 1287/125000000) (ψ := -460977/1000000) 203 154
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t116 : ((-262137839887/5000000000000 : ℚ) : ℝ) ≤ stT203 116 := by
  have hc : ((-282331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262137839887/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-282331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c117 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((181939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1070621/10000000) (δ := 10207/1000000000) (ψ := -460977/1000000) 203 154
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t117 : ((336386721/4000000000 : ℚ) : ℝ) ≤ stT203 117 := by
  have hc : ((181929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336386721/4000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((181929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c118 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((134027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3248559/10000000) (δ := 2549/250000000) (ψ := -460977/1000000) 203 154
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t118 : ((30839689287/1250000000000 : ℚ) : ℝ) ≤ stT203 118 := by
  have hc : ((67001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30839689287/1250000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((67001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c119 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-991679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 241/320) (δ := 2549/250000000) (ψ := -460977/1000000) 203 154
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t119 : ((-909116982571/10000000000000 : ℚ) : ℝ) ≤ stT203 119 := by
  have hc : ((-991729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-909116982571/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-991729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c120 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3929801/10000000) (δ := 10189/1000000000) (ψ := -460977/1000000) 203 155
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t120 : ((-535855277/5000000000000 : ℚ) : ℝ) ≤ stT203 120 := by
  have hc : ((-587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-535855277/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c121 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((248413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3523/125000) (δ := 10189/1000000000) (ψ := -460977/1000000) 203 155
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t121 : ((45163682109/500000000000 : ℚ) : ℝ) ≤ stT203 121 := by
  have hc : ((496801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45163682109/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((496801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c122 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-21113/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4458819/10000000) (δ := 5107/500000000) (ψ := -460977/1000000) 203 155
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t122 : ((-4779837561/250000000000 : ℚ) : ℝ) ≤ stT203 122 := by
  have hc : ((-10559/50000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4779837561/250000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-10559/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c123 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-955607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -710627/1000000) (δ := 10281/1000000000) (ψ := -460977/1000000) 203 156
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t123 : ((-86168724719/1000000000000 : ℚ) : ℝ) ≤ stT203 123 := by
  have hc : ((-955657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86168724719/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-955657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c124 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((181749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2996941/10000000) (δ := 10281/1000000000) (ψ := -460977/1000000) 203 156
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t124 : ((20399109603/625000000000 : ℚ) : ℝ) ≤ stT203 124 := by
  have hc : ((45431/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20399109603/625000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((45431/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c125 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((90823/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1079401/10000000) (δ := 5111/500000000) (ψ := -460977/1000000) 203 156
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t125 : ((40615035643/500000000000 : ℚ) : ℝ) ≤ stT203 125 := by
  have hc : ((45409/50000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40615035643/500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((45409/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c126 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-57557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2561631/5000000) (δ := 10281/1000000000) (ψ := -460977/1000000) 203 156
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t126 : ((-205125720363/5000000000000 : ℚ) : ℝ) ≤ stT203 126 := by
  have hc : ((-230253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205125720363/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-230253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c127 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-871547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6572863/10000000) (δ := 5137/500000000) (ψ := -460977/1000000) 203 157
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t127 : ((-773417699129/10000000000000 : ℚ) : ℝ) ≤ stT203 127 := by
  have hc : ((-871597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-773417699129/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-871597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c128 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((254413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2592439/10000000) (δ := 5137/500000000) (ψ := -460977/1000000) 203 157
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t128 : ((56212307151/1250000000000 : ℚ) : ℝ) ≤ stT203 128 := by
  have hc : ((63597/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56212307151/1250000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((63597/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c129 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((42813/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 339257/2500000) (δ := 10229/1000000000) (ψ := -460977/1000000) 203 157
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t129 : ((1507700189/20000000000 : ℚ) : ℝ) ≤ stT203 129 := by
  have hc : ((85621/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1507700189/20000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((85621/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c130 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-32111/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5275943/10000000) (δ := 10229/1000000000) (ψ := -460977/1000000) 203 157
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t130 : ((-225327858867/5000000000000 : ℚ) : ℝ) ≤ stT203 130 := by
  have hc : ((-256913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225327858867/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-256913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c131 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-54103/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6543099/10000000) (δ := 10267/1000000000) (ψ := -460977/1000000) 203 158
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t131 : ((-75636467109/1000000000000 : ℚ) : ℝ) ≤ stT203 131 := by
  have hc : ((-432849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75636467109/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-432849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c132 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((238523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670941/2500000) (δ := 2559/250000000) (ψ := -460977/1000000) 203 158
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t132 : ((25948224653/625000000000 : ℚ) : ℝ) ≤ stT203 132 := by
  have hc : ((119249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25948224653/625000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((119249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c133 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((224171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28661/250000) (δ := 2559/250000000) (ψ := -460977/1000000) 203 158
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t133 : ((388739705553/5000000000000 : ℚ) : ℝ) ≤ stT203 133 := by
  have hc : ((448317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((388739705553/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((448317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c134 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-3177/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 989589/2000000) (δ := 5109/250000000) (ψ := -460977/1000000) 203 158
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t134 : ((-13724286803/400000000000 : ℚ) : ℝ) ≤ stT203 134 := by
  have hc : ((-15887/40000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13724286803/400000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-15887/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c135 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-470219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6986781/10000000) (δ := 10343/1000000000) (ψ := -460977/1000000) 203 159
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t135 : ((-101180402943/1250000000000 : ℚ) : ℝ) ≤ stT203 135 := by
  have hc : ((-117561/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101180402943/1250000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-117561/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c136 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((270819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3241381/10000000) (δ := 513/50000000) (ψ := -460977/1000000) 203 159
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t136 : ((58045562837/2500000000000 : ℚ) : ℝ) ≤ stT203 136 := by
  have hc : ((270769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58045562837/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((270769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c137 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((490941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95323/2000000) (δ := 127/12500000) (ψ := -460977/1000000) 203 159
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t137 : ((104854380253/1250000000000 : ℚ) : ℝ) ≤ stT203 137 := by
  have hc : ((122729/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104854380253/1250000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((122729/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c138 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-96059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 416751/1000000) (δ := 513/50000000) (ψ := -460977/1000000) 203 159
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t138 : ((-81813459013/10000000000000 : ℚ) : ℝ) ≤ stT203 138 := by
  have hc : ((-96109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81813459013/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-96109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c139 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-999961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7831813/10000000) (δ := 10343/1000000000) (ψ := -460977/1000000) 203 159
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t139 : ((-848198330079/10000000000000 : ℚ) : ℝ) ≤ stT203 139 := by
  have hc : ((-1000011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-848198330079/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-1000011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c140 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-124137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4238137/10000000) (δ := 10153/1000000000) (ψ := -460977/1000000) 203 160
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t140 : ((-20991452797/2000000000000 : ℚ) : ℝ) ≤ stT203 140 := by
  have hc : ((-124187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20991452797/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-124187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c141 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((121101/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78257/1250000) (δ := 207/20000000) (ψ := -460977/1000000) 203 160
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t141 : ((407920259229/5000000000000 : ℚ) : ℝ) ≤ stT203 141 := by
  have hc : ((484379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407920259229/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((484379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c142 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((18851/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 740137/2500000) (δ := 207/20000000) (ψ := -460977/1000000) 203 160
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t142 : ((31634606157/1000000000000 : ℚ) : ℝ) ≤ stT203 142 := by
  have hc : ((37697/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31634606157/1000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((37697/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c143 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-215347/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326099/500000) (δ := 207/20000000) (ψ := -460977/1000000) 203 160
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t143 : ((-360185748717/5000000000000 : ℚ) : ℝ) ≤ stT203 143 := by
  have hc : ((-430719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-360185748717/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-430719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c144 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-635743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5649419/10000000) (δ := 10257/1000000000) (ψ := -460977/1000000) 203 161
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t144 : ((-264913961931/5000000000000 : ℚ) : ℝ) ≤ stT203 144 := by
  have hc : ((-635793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264913961931/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-635793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c145 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((656289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1068633/5000000) (δ := 5173/500000000) (ψ := -460977/1000000) 203 161
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t145 : ((272488151253/5000000000000 : ℚ) : ℝ) ≤ stT203 145 := by
  have hc : ((656239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272488151253/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((656239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c146 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((428779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1350731/10000000) (δ := 5123/500000000) (ψ := -460977/1000000) 203 161
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t146 : ((35483895417/500000000000 : ℚ) : ℝ) ≤ stT203 146 := by
  have hc : ((214377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35483895417/500000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((214377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c147 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-173867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38519/80000) (δ := 5173/500000000) (ψ := -460977/1000000) 203 161
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t147 : ((-35855965251/1250000000000 : ℚ) : ℝ) ≤ stT203 147 := by
  have hc : ((-43473/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35855965251/1250000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-43473/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c148 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-493563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -745239/1000000) (δ := 2033/200000000) (ψ := -460977/1000000) 203 162
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t148 : ((-20286343403/250000000000 : ℚ) : ℝ) ≤ stT203 148 := by
  have hc : ((-123397/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20286343403/250000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-123397/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c149 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-10781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2017417/5000000) (δ := 2053/200000000) (ψ := -460977/1000000) 203 162
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t149 : ((-552648787/156250000000 : ℚ) : ℝ) ≤ stT203 149 := by
  have hc : ((-21587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552648787/156250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-21587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c150 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((241847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -320109/5000000) (δ := 5169/500000000) (ψ := -460977/1000000) 203 162
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t150 : ((24682112739/312500000000 : ℚ) : ℝ) ≤ stT203 150 := by
  have hc : ((483669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24682112739/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((483669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c151 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((46003/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2731917/10000000) (δ := 2033/200000000) (ψ := -460977/1000000) 203 162
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t151 : ((4679077553/125000000000 : ℚ) : ℝ) ≤ stT203 151 := by
  have hc : ((22999/50000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4679077553/125000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((22999/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c152 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-759089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1520443/2500000) (δ := 5119/500000000) (ψ := -460977/1000000) 203 162
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t152 : ((-153935929003/2500000000000 : ℚ) : ℝ) ≤ stT203 152 := by
  have hc : ((-759139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153935929003/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-759139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c153 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-406279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6298311/10000000) (δ := 10331/1000000000) (ψ := -460977/1000000) 203 163
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t153 : ((-10264927741/156250000000 : ℚ) : ℝ) ≤ stT203 153 := by
  have hc : ((-12697/15625 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10264927741/156250000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-12697/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c154 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((365301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29921/100000) (δ := 321/31250000) (ψ := -460977/1000000) 203 163
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t154 : ((147163645661/5000000000000 : ℚ) : ℝ) ≤ stT203 154 := by
  have hc : ((365251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147163645661/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((365251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c155 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((496577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292693/10000000) (δ := 10331/1000000000) (ψ := -460977/1000000) 203 163
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t155 : ((49855000111/625000000000 : ℚ) : ℝ) ≤ stT203 155 := by
  have hc : ((62069/62500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49855000111/625000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((62069/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c156 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((18463/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28451/80000) (δ := 10231/1000000000) (ψ := -460977/1000000) 203 163
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t156 : ((92357577/7812500000 : ℚ) : ℝ) ≤ stT203 156 := by
  have hc : ((73827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92357577/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((73827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c157 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-912307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6799199/10000000) (δ := 321/31250000) (ψ := -460977/1000000) 203 163
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t157 : ((-728140261059/10000000000000 : ℚ) : ℝ) ≤ stT203 157 := by
  have hc : ((-912357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-728140261059/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-912357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c158 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-20223/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2843273/5000000) (δ := 2581/250000000) (ψ := -460977/1000000) 203 164
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t158 : ((-128718499947/2500000000000 : ℚ) : ℝ) ≤ stT203 158 := by
  have hc : ((-323593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128718499947/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-323593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c159 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((272733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2484627/10000000) (δ := 2581/250000000) (ψ := -460977/1000000) 203 164
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t159 : ((54067838027/1250000000000 : ℚ) : ℝ) ≤ stT203 159 := by
  have hc : ((68177/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54067838027/1250000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((68177/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c160 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((192273/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139439/2000000) (δ := 2581/250000000) (ψ := -460977/1000000) 203 164
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t160 : ((151997167647/2000000000000 : ℚ) : ℝ) ≤ stT203 160 := by
  have hc : ((192263/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151997167647/2000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((192263/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c161 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((27123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1929587/5000000) (δ := 639/62500000) (ψ := -460977/1000000) 203 164
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t161 : ((2133650203/1000000000000 : ℚ) : ℝ) ≤ stT203 161 := by
  have hc : ((27073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2133650203/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((27073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c162 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-471219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3500807/5000000) (δ := 639/62500000) (ψ := -460977/1000000) 203 164
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t162 : ((-3702446297/50000000000 : ℚ) : ℝ) ≤ stT203 162 := by
  have hc : ((-117811/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3702446297/50000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-117811/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c163 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-615091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1116649/2000000) (δ := 10217/1000000000) (ψ := -460977/1000000) 203 165
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t163 : ((-481815954801/10000000000000 : ℚ) : ℝ) ≤ stT203 163 := by
  have hc : ((-615141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-481815954801/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-615141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c164 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((27363/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2479273/10000000) (δ := 5143/500000000) (ψ := -460977/1000000) 203 165
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t164 : ((10682469457/250000000000 : ℚ) : ℝ) ≤ stT203 164 := by
  have hc : ((54721/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10682469457/250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((54721/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c165 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((485391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 605819/10000000) (δ := 10217/1000000000) (ψ := -460977/1000000) 203 165
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t165 : ((94464115067/1250000000000 : ℚ) : ℝ) ≤ stT203 165 := by
  have hc : ((242683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94464115067/1250000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((242683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c166 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((50853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1836143/5000000) (δ := 10317/1000000000) (ψ := -460977/1000000) 203 165
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t166 : ((197250761/25000000000 : ℚ) : ℝ) ≤ stT203 166 := by
  have hc : ((12707/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197250761/25000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((12707/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c167 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-449473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3360191/5000000) (δ := 10217/1000000000) (ψ := -460977/1000000) 203 165
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t167 : ((-2717440159/39062500000 : ℚ) : ℝ) ≤ stT203 167 := by
  have hc : ((-224749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2717440159/39062500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-224749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c168 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-5807/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1191551/2000000) (δ := 10293/1000000000) (ψ := -460977/1000000) 203 166
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t168 : ((-22402539129/400000000000 : ℚ) : ℝ) ≤ stT203 168 := by
  have hc : ((-29037/40000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22402539129/400000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-29037/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c169 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((382461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -736461/2500000) (δ := 10293/1000000000) (ψ := -460977/1000000) 203 166
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t169 : ((29416201353/1000000000000 : ℚ) : ℝ) ≤ stT203 169 := by
  have hc : ((382411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29416201353/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((382411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c170 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((499907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48253/10000000) (δ := 1031/100000000) (ψ := -460977/1000000) 203 166
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t170 : ((47923937281/625000000000 : ℚ) : ℝ) ≤ stT203 170 := by
  have hc : ((249941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47923937281/625000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((249941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c171 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((353097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378099/1250000) (δ := 10293/1000000000) (ψ := -460977/1000000) 203 166
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t171 : ((269981748793/10000000000000 : ℚ) : ℝ) ≤ stT203 171 := by
  have hc : ((353047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269981748793/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((353047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c172 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-91631/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5983973/10000000) (δ := 1031/100000000) (ψ := -460977/1000000) 203 166
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t172 : ((-279491046657/5000000000000 : ℚ) : ℝ) ≤ stT203 172 := by
  have hc : ((-366549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279491046657/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-366549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c173 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-454731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3390981/5000000) (δ := 10303/1000000000) (ψ := -460977/1000000) 203 167
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t173 : ((-43218077527/625000000000 : ℚ) : ℝ) ≤ stT203 173 := by
  have hc : ((-113689/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43218077527/625000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-113689/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c174 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((28039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -964221/2500000) (δ := 10203/1000000000) (ψ := -460977/1000000) 203 167
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t174 : ((10609202461/5000000000000 : ℚ) : ℝ) ≤ stT203 174 := by
  have hc : ((27989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10609202461/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((27989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c175 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((928879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -474277/5000000) (δ := 10303/1000000000) (ψ := -460977/1000000) 203 167
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t175 : ((87765981039/1250000000000 : ℚ) : ℝ) ≤ stT203 175 := by
  have hc : ((928829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87765981039/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((928829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c176 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((712829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1943181/10000000) (δ := 10303/1000000000) (ψ := -460977/1000000) 203 167
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t176 : ((268638564531/5000000000000 : ℚ) : ℝ) ≤ stT203 176 := by
  have hc : ((712779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268638564531/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((712779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c177 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-174561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192743/400000) (δ := 51/5000000) (ψ := -460977/1000000) 203 167
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t177 : ((-65613521571/2500000000000 : ℚ) : ℝ) ≤ stT203 177 := by
  have hc : ((-87293/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65613521571/2500000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-87293/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c178 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-249379/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239929/312500) (δ := 10303/1000000000) (ψ := -460977/1000000) 203 167
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t178 : ((-93463454889/1250000000000 : ℚ) : ℝ) ≤ stT203 178 := by
  have hc : ((-498783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93463454889/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-498783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c179 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-482959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1296767/2500000) (δ := 2059/200000000) (ψ := -460977/1000000) 203 168
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t179 : ((-90254578731/2500000000000 : ℚ) : ℝ) ≤ stT203 179 := by
  have hc : ((-483009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90254578731/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-483009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c180 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((586623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471957/2000000) (δ := 319/31250000) (ψ := -460977/1000000) 203 168
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t180 : ((87441023683/2000000000000 : ℚ) : ℝ) ≤ stT203 180 := by
  have hc : ((586573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87441023683/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((586573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c181 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((98371/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 225933/5000000) (δ := 2059/200000000) (ψ := -460977/1000000) 203 168
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t181 : ((18278714401/250000000000 : ℚ) : ℝ) ≤ stT203 181 := by
  have hc : ((49183/50000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18278714401/250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((49183/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c182 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((134137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811997/2500000) (δ := 2059/200000000) (ψ := -460977/1000000) 203 168
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t182 : ((3106574559/156250000000 : ℚ) : ℝ) ≤ stT203 182 := by
  have hc : ((4191/15625 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3106574559/156250000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((4191/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c183 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-149027/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1205767/2000000) (δ := 2577/250000000) (ψ := -460977/1000000) 203 168
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t183 : ((-55085714607/1000000000000 : ℚ) : ℝ) ≤ stT203 183 := by
  have hc : ((-149037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55085714607/1000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-149037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c184 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-58129/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6913457/10000000) (δ := 643/62500000) (ψ := -460977/1000000) 203 169
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t184 : ((-34284467097/500000000000 : ℚ) : ℝ) ≤ stT203 184 := by
  have hc : ((-465057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34284467097/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-465057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c185 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-47083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1040689/2500000) (δ := 2547/250000000) (ψ := -460977/1000000) 203 169
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t185 : ((-1731725411/250000000000 : ℚ) : ℝ) ≤ stT203 185 := by
  have hc : ((-11777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1731725411/250000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-11777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c186 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((168297/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57077/400000) (δ := 2547/250000000) (ψ := -460977/1000000) 203 169
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t186 : ((24678783689/400000000000 : ℚ) : ℝ) ≤ stT203 186 := by
  have hc : ((168287/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24678783689/400000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((168287/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c187 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((108619/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129429/1000000) (δ := 2547/250000000) (ψ := -460977/1000000) 203 169
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t187 : ((39712731459/625000000000 : ℚ) : ℝ) ≤ stT203 187 := by
  have hc : ((434451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39712731459/625000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((434451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c188 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-1183/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200047/500000) (δ := 2043/200000000) (ψ := -460977/1000000) 203 169
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t188 : ((-6914001/3200000000 : ℚ) : ℝ) ≤ stT203 188 := by
  have hc : ((-237/8000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6914001/3200000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-237/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c189 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-13971/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3346639/5000000) (δ := 2547/250000000) (ψ := -460977/1000000) 203 169
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t189 : ((-325215228121/5000000000000 : ℚ) : ℝ) ≤ stT203 189 := by
  have hc : ((-447097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325215228121/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-447097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c190 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-51337/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198019/312500) (δ := 10281/1000000000) (ψ := -460977/1000000) 203 170
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t190 : ((-297968638917/5000000000000 : ℚ) : ℝ) ≤ stT203 190 := by
  have hc : ((-410721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297968638917/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-410721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c191 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((50803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3672537/10000000) (δ := 5111/500000000) (ψ := -460977/1000000) 203 170
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t191 : ((9185410143/1250000000000 : ℚ) : ℝ) ≤ stT203 191 := by
  have hc : ((25389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9185410143/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((25389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c192 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((917531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1022423/10000000) (δ := 10181/1000000000) (ψ := -460977/1000000) 203 170
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t192 : ((662134110447/10000000000000 : ℚ) : ℝ) ≤ stT203 192 := by
  have hc : ((917481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((662134110447/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((917481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c193 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((399377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806969/5000000) (δ := 10181/1000000000) (ψ := -460977/1000000) 203 170
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t193 : ((7186488997/125000000000 : ℚ) : ℝ) ≤ stT203 193 := by
  have hc : ((49919/62500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7186488997/125000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((49919/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c194 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-61783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2118349/5000000) (δ := 10181/1000000000) (ψ := -460977/1000000) 203 170
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t194 : ((-2773475617/312500000000 : ℚ) : ℝ) ≤ stT203 194 := by
  have hc : ((-3863/31250 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2773475617/312500000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-3863/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c195 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-919807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6845959/10000000) (δ := 5161/500000000) (ψ := -460977/1000000) 203 170
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t195 : ((-131744679111/2000000000000 : ℚ) : ℝ) ≤ stT203 195 := by
  have hc : ((-919857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131744679111/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-919857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c196 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-804979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6266091/10000000) (δ := 10329/1000000000) (ψ := -460977/1000000) 203 171
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t196 : ((-287510472147/5000000000000 : ℚ) : ℝ) ≤ stT203 196 := by
  have hc : ((-805029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287510472147/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-805029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c197 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((97293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3683373/10000000) (δ := 10229/1000000000) (ψ := -460977/1000000) 203 171
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t197 : ((6928272021/1000000000000 : ℚ) : ℝ) ≤ stT203 197 := by
  have hc : ((97243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6928272021/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((97243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c198 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((225599/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278437/2500000) (δ := 10329/1000000000) (ψ := -460977/1000000) 203 171
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t198 : ((320634664737/5000000000000 : ℚ) : ℝ) ≤ stT203 198 := by
  have hc : ((451173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320634664737/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((451173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c199 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((104751/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288587/2000000) (δ := 5087/500000000) (ψ := -460977/1000000) 203 171
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t199 : ((297006252499/5000000000000 : ℚ) : ℝ) ≤ stT203 199 := by
  have hc : ((418979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297006252499/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((418979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c200 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-23913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3986779/10000000) (δ := 10229/1000000000) (ψ := -460977/1000000) 203 171
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t200 : ((-16944405041/10000000000000 : ℚ) : ℝ) ≤ stT203 200 := by
  have hc : ((-23963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16944405041/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-23963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c201 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-34423/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3258993/5000000) (δ := 10229/1000000000) (ψ := -460977/1000000) 203 171
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t201 : ((-485630721/8000000000 : ℚ) : ℝ) ≤ stT203 201 := by
  have hc : ((-1377/1600 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485630721/8000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-1377/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c202 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-55637/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6671407/10000000) (δ := 2559/250000000) (ψ := -460977/1000000) 203 172
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t202 : ((-156593122679/2500000000000 : ℚ) : ℝ) ≤ stT203 202 := by
  have hc : ((-445121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156593122679/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-445121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c203 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-23787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -208261/500000) (δ := 10167/1000000000) (ψ := -460977/1000000) 203 172
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t203 : ((-33407976937/5000000000000 : ℚ) : ℝ) ≤ stT203 203 := by
  have hc : ((-47599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33407976937/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-47599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c204 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((196181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334273/2000000) (δ := 10167/1000000000) (ψ := -460977/1000000) 203 172
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t204 : ((13734541359/250000000000 : ℚ) : ℝ) ≤ stT203 204 := by
  have hc : ((392337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13734541359/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((392337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c205 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((94793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81031/1000000) (δ := 10167/1000000000) (ψ := -460977/1000000) 203 172
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t205 : ((1655069571/25000000000 : ℚ) : ℝ) ≤ stT203 205 := by
  have hc : ((23697/25000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1655069571/25000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((23697/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c206 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((255953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3279907/10000000) (δ := 323/31250000) (ψ := -460977/1000000) 203 172
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t206 : ((178296064899/10000000000000 : ℚ) : ℝ) ≤ stT203 206 := by
  have hc : ((255903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178296064899/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((255903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c207 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-662547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2868763/5000000) (δ := 10167/1000000000) (ψ := -460977/1000000) 203 172
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t207 : ((-460537382253/10000000000000 : ℚ) : ℝ) ≤ stT203 207 := by
  have hc : ((-662597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-460537382253/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-662597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c208 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-198267/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3762321/5000000) (δ := 1293/125000000) (ψ := -460977/1000000) 203 173
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t208 : ((-1074066509/15625000000 : ℚ) : ℝ) ≤ stT203 208 := by
  have hc : ((-198277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1074066509/15625000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-198277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c209 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-448809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5090571/10000000) (δ := 10159/1000000000) (ψ := -460977/1000000) 203 173
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t209 : ((-62096500637/2000000000000 : ℚ) : ℝ) ≤ stT203 209 := by
  have hc : ((-448859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62096500637/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-448859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c210 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((60317/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2668121/10000000) (δ := 2561/250000000) (ψ := -460977/1000000) 203 173
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t210 : ((33294670159/1000000000000 : ℚ) : ℝ) ≤ stT203 210 := by
  have hc : ((241243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33294670159/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((241243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c211 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((994713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32149/1250000) (δ := 10259/1000000000) (ψ := -460977/1000000) 203 173
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t211 : ((171188464941/2500000000000 : ℚ) : ℝ) ≤ stT203 211 := by
  have hc : ((994663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171188464941/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((994663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c212 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((654763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2142319/10000000) (δ := 10159/1000000000) (ψ := -460977/1000000) 203 173
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t212 : ((224829098913/5000000000000 : ℚ) : ℝ) ≤ stT203 212 := by
  have hc : ((654713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224829098913/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((654713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c213 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-23909/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4530563/10000000) (δ := 10259/1000000000) (ψ := -460977/1000000) 203 173
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t213 : ((-8192804873/500000000000 : ℚ) : ℝ) ≤ stT203 213 := by
  have hc : ((-11957/50000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8192804873/500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-11957/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c214 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-929207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6907643/10000000) (δ := 1293/125000000) (ψ := -460977/1000000) 203 173
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t214 : ((-317613537801/5000000000000 : ℚ) : ℝ) ≤ stT203 214 := by
  have hc : ((-929257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-317613537801/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-929257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c215 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-843059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1608589/2500000) (δ := 2563/250000000) (ψ := -460977/1000000) 203 174
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t215 : ((-114999224491/2000000000000 : ℚ) : ℝ) ≤ stT203 215 := by
  have hc : ((-843109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114999224491/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-843109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c216 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-60907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4079353/10000000) (δ := 2563/250000000) (ψ := -460977/1000000) 203 174
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t216 : ((-20737998099/5000000000000 : ℚ) : ℝ) ≤ stT203 216 := by
  have hc : ((-60957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20737998099/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-60957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c217 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((768627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1735261/10000000) (δ := 1269/125000000) (ψ := -460977/1000000) 203 174
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t217 : ((130435971247/2500000000000 : ℚ) : ℝ) ≤ stT203 217 := by
  have hc : ((768577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130435971247/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((768577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c218 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((971521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74759/1250000) (δ := 10251/1000000000) (ψ := -460977/1000000) 203 174
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t218 : ((131592547247/2000000000000 : ℚ) : ℝ) ≤ stT203 218 := by
  have hc : ((971471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131592547247/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((971471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c219 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((391717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2920747/10000000) (δ := 1269/125000000) (ψ := -460977/1000000) 203 174
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t219 : ((264663883579/10000000000000 : ℚ) : ℝ) ≤ stT203 219 := by
  have hc : ((391667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264663883579/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((391667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c220 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-498901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327051/625000) (δ := 10351/1000000000) (ψ := -460977/1000000) 203 174
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t220 : ((-1681963821/50000000000 : ℚ) : ℝ) ≤ stT203 220 := by
  have hc : ((-498951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1681963821/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-498951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c221 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-495921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 753443/1000000) (δ := 10351/1000000000) (ψ := -460977/1000000) 203 174
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t221 : ((-166804741829/2500000000000 : ℚ) : ℝ) ≤ stT203 221 := by
  have hc : ((-247973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166804741829/2500000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-247973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c222 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-704809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2941187/5000000) (δ := 5129/500000000) (ψ := -460977/1000000) 203 175
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t222 : ((-473071051863/10000000000000 : ℚ) : ℝ) ≤ stT203 222 := by
  have hc : ((-704859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473071051863/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-704859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c223 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((64921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1800733/5000000) (δ := 5129/500000000) (ψ := -460977/1000000) 203 175
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t223 : ((339512043/39062500000 : ℚ) : ℝ) ≤ stT203 223 := by
  have hc : ((2028/15625 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339512043/39062500000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((2028/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c224 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((21541/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1330759/10000000) (δ := 5079/500000000) (ψ := -460977/1000000) 203 175
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t224 : ((57567394327/1000000000000 : ℚ) : ℝ) ≤ stT203 224 := by
  have hc : ((86159/100000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57567394327/1000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((86159/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c225 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((116453/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 929849/10000000) (δ := 5079/500000000) (ψ := -460977/1000000) 203 175
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t225 : ((155262178071/2500000000000 : ℚ) : ℝ) ≤ stT203 225 := by
  have hc : ((465787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155262178071/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((465787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c226 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((18389/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3180383/10000000) (δ := 4069/200000000) (ψ := -460977/1000000) 203 175
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t226 : ((9784080153/500000000000 : ℚ) : ℝ) ≤ stT203 226 := by
  have hc : ((147087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9784080153/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((147087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c227 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-56267/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5421021/10000000) (δ := 5079/500000000) (ψ := -460977/1000000) 203 175
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t227 : ((-583579327/15625000000 : ℚ) : ℝ) ≤ stT203 227 := by
  have hc : ((-3517/6250 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583579327/15625000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-3517/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c228 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-996731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1912947/2500000) (δ := 5079/500000000) (ψ := -460977/1000000) 203 175
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t228 : ((-660135162527/10000000000000 : ℚ) : ℝ) ≤ stT203 228 := by
  have hc : ((-996781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660135162527/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-996781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c229 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-172821/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -364697/625000) (δ := 2053/200000000) (ψ := -460977/1000000) 203 176
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t229 : ((-228423321273/5000000000000 : ℚ) : ℝ) ≤ stT203 229 := by
  have hc : ((-345667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228423321273/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-345667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c230 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((12097/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3623823/10000000) (δ := 5169/500000000) (ψ := -460977/1000000) 203 176
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t230 : ((99665287/12500000000 : ℚ) : ℝ) ≤ stT203 230 := by
  have hc : ((3023/25000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99665287/12500000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((3023/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c231 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((84253/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284417/2000000) (δ := 5169/500000000) (ψ := -460977/1000000) 203 176
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t231 : ((6928881981/125000000000 : ℚ) : ℝ) ≤ stT203 231 := by
  have hc : ((10531/12500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6928881981/125000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((10531/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c232 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((29779/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12033/156250) (δ := 5169/500000000) (ψ := -460977/1000000) 203 176
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t232 : ((78199362387/1250000000000 : ℚ) : ℝ) ≤ stT203 232 := by
  have hc : ((476439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78199362387/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((476439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c233 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((94961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2952921/10000000) (δ := 2053/200000000) (ψ := -460977/1000000) 203 176
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t233 : ((124405512537/5000000000000 : ℚ) : ℝ) ≤ stT203 233 := by
  have hc : ((189897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124405512537/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((189897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c234 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-230783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5126391/10000000) (δ := 2033/200000000) (ψ := -460977/1000000) 203 176
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t234 : ((-18860504571/625000000000 : ℚ) : ℝ) ≤ stT203 234 := by
  have hc : ((-28851/62500 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18860504571/625000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-28851/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c235 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-974713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3645287/5000000) (δ := 2033/200000000) (ψ := -460977/1000000) 203 176
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t235 : ((-635866173027/10000000000000 : ℚ) : ℝ) ≤ stT203 235 := by
  have hc : ((-974763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-635866173027/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-974763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c236 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-8041/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782799/1250000) (δ := 2543/250000000) (ψ := -460977/1000000) 203 177
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t236 : ((-2093829687/40000000000 : ℚ) : ℝ) ≤ stT203 236 := by
  have hc : ((-16083/20000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2093829687/40000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-16083/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c237 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-75743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -411653/1000000) (δ := 10231/1000000000) (ψ := -460977/1000000) 203 177
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t237 : ((-4923285901/1000000000000 : ℚ) : ℝ) ≤ stT203 237 := by
  have hc : ((-75793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4923285901/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-75793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c238 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((175627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1979701/10000000) (δ := 2543/250000000) (ψ := -460977/1000000) 203 177
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t238 : ((227667691487/5000000000000 : ℚ) : ℝ) ≤ stT203 238 := by
  have hc : ((351229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227667691487/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((351229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c239 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((249561/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37049/2500000) (δ := 321/31250000) (ψ := -460977/1000000) 203 177
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t239 : ((161419449031/2500000000000 : ℚ) : ℝ) ≤ stT203 239 := by
  have hc : ((499097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161419449031/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((499097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c240 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((616203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2267211/10000000) (δ := 10231/1000000000) (ψ := -460977/1000000) 203 177
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t240 : ((397724913041/10000000000000 : ℚ) : ℝ) ≤ stT203 240 := by
  have hc : ((616153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397724913041/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((616153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c241 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-179189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1094349/2500000) (δ := 10231/1000000000) (ψ := -460977/1000000) 203 177
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t241 : ((-115458056523/10000000000000 : ℚ) : ℝ) ≤ stT203 241 := by
  have hc : ((-179239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115458056523/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-179239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c242 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-852497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619713/2500000) (δ := 10231/1000000000) (ψ := -460977/1000000) 203 177
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t242 : ((-21921541011/400000000000 : ℚ) : ℝ) ≤ stT203 242 := by
  have hc : ((-852547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21921541011/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-852547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c243 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-959081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7136333/10000000) (δ := 10279/1000000000) (ψ := -460977/1000000) 203 178
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t243 : ((-615283495631/10000000000000 : ℚ) : ℝ) ≤ stT203 243 := by
  have hc : ((-959131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615283495631/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-959131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c244 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-54377/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263033/2500000) (δ := 10279/1000000000) (ψ := -460977/1000000) 203 178
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t244 : ((-27852272721/1000000000000 : ℚ) : ℝ) ≤ stT203 244 := by
  have hc : ((-217533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27852272721/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-217533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c245 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((371109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2976483/10000000) (δ := 2553/125000000) (ψ := -460977/1000000) 203 178
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t245 : ((59265172421/2500000000000 : ℚ) : ℝ) ≤ stT203 245 := by
  have hc : ((371059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59265172421/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((371059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c246 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((467293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -454629/5000000) (δ := 2581/250000000) (ψ := -460977/1000000) 203 178
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t246 : ((9309964449/156250000000 : ℚ) : ℝ) ≤ stT203 246 := by
  have hc : ((116817/125000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9309964449/156250000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((116817/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c247 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((896129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8981/78125) (δ := 2581/250000000) (ψ := -460977/1000000) 203 178
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t247 : ((142540182609/2500000000000 : ℚ) : ℝ) ≤ stT203 247 := by
  have hc : ((896079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142540182609/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((896079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c248 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((8959/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3200071/10000000) (δ := 2581/250000000) (ψ := -460977/1000000) 203 178
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t248 : ((18201513/1000000000 : ℚ) : ℝ) ≤ stT203 248 := by
  have hc : ((143319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18201513/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((143319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c249 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-251093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2621151/5000000) (δ := 639/62500000) (ψ := -460977/1000000) 203 178
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t249 : ((-3182795091/100000000000 : ℚ) : ℝ) ≤ stT203 249 := by
  have hc : ((-125559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3182795091/100000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-125559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_c250 :
    |Real.cos (((203 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((-121679/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7276413/10000000) (δ := 10179/1000000000) (ψ := -460977/1000000) 203 178
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st203_t250 : ((-38480283237/625000000000 : ℚ) : ℝ) ≤ stT203 250 := by
  have hc : ((-486741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((203 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st203_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38480283237/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-486741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st203_p1 : ((55973/62500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT203 (i+1) := by
  rw [Finset.sum_range_one]
  exact st203_t1

theorem st203_p2 : ((506944978449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT203 (i+1))
      = (∑ i ∈ Finset.range 1, stT203 (i+1)) + stT203 2 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 1
    simpa using h
  have hprev := st203_p1
  have hstep := st203_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p3 : ((-3229566144501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT203 (i+1))
      = (∑ i ∈ Finset.range 2, stT203 (i+1)) + stT203 3 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 2
    simpa using h
  have hprev := st203_p2
  have hstep := st203_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p4 : ((14873855499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT203 (i+1))
      = (∑ i ∈ Finset.range 3, stT203 (i+1)) + stT203 4 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 3
    simpa using h
  have hprev := st203_p3
  have hstep := st203_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p5 : ((1009786723981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT203 (i+1))
      = (∑ i ∈ Finset.range 4, stT203 (i+1)) + stT203 5 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 4
    simpa using h
  have hprev := st203_p4
  have hstep := st203_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p6 : ((1000960852913/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT203 (i+1))
      = (∑ i ∈ Finset.range 5, stT203 (i+1)) + stT203 6 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 5
    simpa using h
  have hprev := st203_p5
  have hstep := st203_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p7 : ((577246923697/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT203 (i+1))
      = (∑ i ∈ Finset.range 6, stT203 (i+1)) + stT203 7 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 6
    simpa using h
  have hprev := st203_p6
  have hstep := st203_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p8 : ((2847842254779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT203 (i+1))
      = (∑ i ∈ Finset.range 7, stT203 (i+1)) + stT203 8 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 7
    simpa using h
  have hprev := st203_p7
  have hstep := st203_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p9 : ((452264022219/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT203 (i+1))
      = (∑ i ∈ Finset.range 8, stT203 (i+1)) + stT203 9 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 8
    simpa using h
  have hprev := st203_p8
  have hstep := st203_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p10 : ((2845129686849/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT203 (i+1))
      = (∑ i ∈ Finset.range 9, stT203 (i+1)) + stT203 10 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 9
    simpa using h
  have hprev := st203_p9
  have hstep := st203_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p11 : ((169769091297/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT203 (i+1))
      = (∑ i ∈ Finset.range 10, stT203 (i+1)) + stT203 11 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 10
    simpa using h
  have hprev := st203_p10
  have hstep := st203_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p12 : ((3346249667913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT203 (i+1))
      = (∑ i ∈ Finset.range 11, stT203 (i+1)) + stT203 12 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 11
    simpa using h
  have hprev := st203_p11
  have hstep := st203_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p13 : ((4644676173663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT203 (i+1))
      = (∑ i ∈ Finset.range 12, stT203 (i+1)) + stT203 13 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 12
    simpa using h
  have hprev := st203_p12
  have hstep := st203_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p14 : ((789667509393/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT203 (i+1))
      = (∑ i ∈ Finset.range 13, stT203 (i+1)) + stT203 14 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 13
    simpa using h
  have hprev := st203_p13
  have hstep := st203_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p15 : ((1107050500851/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT203 (i+1))
      = (∑ i ∈ Finset.range 14, stT203 (i+1)) + stT203 15 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 14
    simpa using h
  have hprev := st203_p14
  have hstep := st203_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p16 : ((1020946105917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT203 (i+1))
      = (∑ i ∈ Finset.range 15, stT203 (i+1)) + stT203 16 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 15
    simpa using h
  have hprev := st203_p15
  have hstep := st203_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p17 : ((443189332523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT203 (i+1))
      = (∑ i ∈ Finset.range 16, stT203 (i+1)) + stT203 17 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 16
    simpa using h
  have hprev := st203_p16
  have hstep := st203_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p18 : ((-27464751879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT203 (i+1))
      = (∑ i ∈ Finset.range 17, stT203 (i+1)) + stT203 18 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 17
    simpa using h
  have hprev := st203_p17
  have hstep := st203_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p19 : ((60386979699/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT203 (i+1))
      = (∑ i ∈ Finset.range 18, stT203 (i+1)) + stT203 19 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 18
    simpa using h
  have hprev := st203_p18
  have hstep := st203_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p20 : ((407636758761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT203 (i+1))
      = (∑ i ∈ Finset.range 19, stT203 (i+1)) + stT203 20 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 19
    simpa using h
  have hprev := st203_p19
  have hstep := st203_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p21 : ((1184716953/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT203 (i+1))
      = (∑ i ∈ Finset.range 20, stT203 (i+1)) + stT203 21 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 20
    simpa using h
  have hprev := st203_p20
  have hstep := st203_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p22 : ((1003351948929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT203 (i+1))
      = (∑ i ∈ Finset.range 21, stT203 (i+1)) + stT203 22 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 21
    simpa using h
  have hprev := st203_p21
  have hstep := st203_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p23 : ((519847467563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT203 (i+1))
      = (∑ i ∈ Finset.range 22, stT203 (i+1)) + stT203 23 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 22
    simpa using h
  have hprev := st203_p22
  have hstep := st203_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p24 : ((537336820451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT203 (i+1))
      = (∑ i ∈ Finset.range 23, stT203 (i+1)) + stT203 24 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 23
    simpa using h
  have hprev := st203_p23
  have hstep := st203_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p25 : ((2345458820451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT203 (i+1))
      = (∑ i ∈ Finset.range 24, stT203 (i+1)) + stT203 25 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 24
    simpa using h
  have hprev := st203_p24
  have hstep := st203_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p26 : ((1321418470531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT203 (i+1))
      = (∑ i ∈ Finset.range 25, stT203 (i+1)) + stT203 26 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 25
    simpa using h
  have hprev := st203_p25
  have hstep := st203_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p27 : ((-4820910761/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT203 (i+1))
      = (∑ i ∈ Finset.range 26, stT203 (i+1)) + stT203 27 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 26
    simpa using h
  have hprev := st203_p26
  have hstep := st203_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p28 : ((-139700831389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT203 (i+1))
      = (∑ i ∈ Finset.range 27, stT203 (i+1)) + stT203 28 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 27
    simpa using h
  have hprev := st203_p27
  have hstep := st203_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p29 : ((266846859391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT203 (i+1))
      = (∑ i ∈ Finset.range 28, stT203 (i+1)) + stT203 29 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 28
    simpa using h
  have hprev := st203_p28
  have hstep := st203_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p30 : ((1152112155471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT203 (i+1))
      = (∑ i ∈ Finset.range 29, stT203 (i+1)) + stT203 30 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 29
    simpa using h
  have hprev := st203_p29
  have hstep := st203_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p31 : ((4085763406649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT203 (i+1))
      = (∑ i ∈ Finset.range 30, stT203 (i+1)) + stT203 31 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 30
    simpa using h
  have hprev := st203_p30
  have hstep := st203_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p32 : ((5780320913291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT203 (i+1))
      = (∑ i ∈ Finset.range 31, stT203 (i+1)) + stT203 32 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 31
    simpa using h
  have hprev := st203_p31
  have hstep := st203_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p33 : ((7465997871339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT203 (i+1))
      = (∑ i ∈ Finset.range 32, stT203 (i+1)) + stT203 33 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 32
    simpa using h
  have hprev := st203_p32
  have hstep := st203_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p34 : ((9180173398419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT203 (i+1))
      = (∑ i ∈ Finset.range 33, stT203 (i+1)) + stT203 34 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 33
    simpa using h
  have hprev := st203_p33
  have hstep := st203_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p35 : ((10756204745463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT203 (i+1))
      = (∑ i ∈ Finset.range 34, stT203 (i+1)) + stT203 35 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 34
    simpa using h
  have hprev := st203_p34
  have hstep := st203_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p36 : ((11746929349173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT203 (i+1))
      = (∑ i ∈ Finset.range 35, stT203 (i+1)) + stT203 36 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 35
    simpa using h
  have hprev := st203_p35
  have hstep := st203_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p37 : ((11607990822303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT203 (i+1))
      = (∑ i ∈ Finset.range 36, stT203 (i+1)) + stT203 37 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 36
    simpa using h
  have hprev := st203_p36
  have hstep := st203_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p38 : ((10284513203413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT203 (i+1))
      = (∑ i ∈ Finset.range 37, stT203 (i+1)) + stT203 38 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 37
    simpa using h
  have hprev := st203_p37
  have hstep := st203_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p39 : ((8805513103343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT203 (i+1))
      = (∑ i ∈ Finset.range 38, stT203 (i+1)) + stT203 39 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 38
    simpa using h
  have hprev := st203_p38
  have hstep := st203_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p40 : ((547014196119/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT203 (i+1))
      = (∑ i ∈ Finset.range 39, stT203 (i+1)) + stT203 40 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 39
    simpa using h
  have hprev := st203_p39
  have hstep := st203_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p41 : ((2556912514347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT203 (i+1))
      = (∑ i ∈ Finset.range 40, stT203 (i+1)) + stT203 41 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 40
    simpa using h
  have hprev := st203_p40
  have hstep := st203_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p42 : ((42911223001/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT203 (i+1))
      = (∑ i ∈ Finset.range 41, stT203 (i+1)) + stT203 42 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 41
    simpa using h
  have hprev := st203_p41
  have hstep := st203_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p43 : ((2426898516969/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT203 (i+1))
      = (∑ i ∈ Finset.range 42, stT203 (i+1)) + stT203 43 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 42
    simpa using h
  have hprev := st203_p42
  have hstep := st203_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p44 : ((4471352436393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT203 (i+1))
      = (∑ i ∈ Finset.range 43, stT203 (i+1)) + stT203 44 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 43
    simpa using h
  have hprev := st203_p43
  have hstep := st203_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p45 : ((10326080208653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT203 (i+1))
      = (∑ i ∈ Finset.range 44, stT203 (i+1)) + stT203 45 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 44
    simpa using h
  have hprev := st203_p44
  have hstep := st203_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p46 : ((2629646931347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT203 (i+1))
      = (∑ i ∈ Finset.range 45, stT203 (i+1)) + stT203 46 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 45
    simpa using h
  have hprev := st203_p45
  have hstep := st203_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p47 : ((17761018149/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT203 (i+1))
      = (∑ i ∈ Finset.range 46, stT203 (i+1)) + stT203 47 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 46
    simpa using h
  have hprev := st203_p46
  have hstep := st203_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p48 : ((4985931405519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT203 (i+1))
      = (∑ i ∈ Finset.range 47, stT203 (i+1)) + stT203 48 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 47
    simpa using h
  have hprev := st203_p47
  have hstep := st203_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p49 : ((10514832648147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT203 (i+1))
      = (∑ i ∈ Finset.range 48, stT203 (i+1)) + stT203 49 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 48
    simpa using h
  have hprev := st203_p48
  have hstep := st203_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p50 : ((9135032131623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT203 (i+1))
      = (∑ i ∈ Finset.range 49, stT203 (i+1)) + stT203 50 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 49
    simpa using h
  have hprev := st203_p49
  have hstep := st203_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p51 : ((10243699620783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT203 (i+1))
      = (∑ i ∈ Finset.range 50, stT203 (i+1)) + stT203 51 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 50
    simpa using h
  have hprev := st203_p50
  have hstep := st203_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p52 : ((10086619561511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT203 (i+1))
      = (∑ i ∈ Finset.range 51, stT203 (i+1)) + stT203 52 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 51
    simpa using h
  have hprev := st203_p51
  have hstep := st203_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p53 : ((9297713680319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT203 (i+1))
      = (∑ i ∈ Finset.range 52, stT203 (i+1)) + stT203 53 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 52
    simpa using h
  have hprev := st203_p52
  have hstep := st203_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p54 : ((10595188740161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT203 (i+1))
      = (∑ i ∈ Finset.range 53, stT203 (i+1)) + stT203 54 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 53
    simpa using h
  have hprev := st203_p53
  have hstep := st203_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p55 : ((9298162780161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT203 (i+1))
      = (∑ i ∈ Finset.range 54, stT203 (i+1)) + stT203 55 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 54
    simpa using h
  have hprev := st203_p54
  have hstep := st203_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p56 : ((10235537341063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT203 (i+1))
      = (∑ i ∈ Finset.range 55, stT203 (i+1)) + stT203 56 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 55
    simpa using h
  have hprev := st203_p55
  have hstep := st203_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p57 : ((2452789573099/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT203 (i+1))
      = (∑ i ∈ Finset.range 56, stT203 (i+1)) + stT203 57 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 56
    simpa using h
  have hprev := st203_p56
  have hstep := st203_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p58 : ((9728628217951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT203 (i+1))
      = (∑ i ∈ Finset.range 57, stT203 (i+1)) + stT203 58 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 57
    simpa using h
  have hprev := st203_p57
  have hstep := st203_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p59 : ((5112614935667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT203 (i+1))
      = (∑ i ∈ Finset.range 58, stT203 (i+1)) + stT203 59 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 58
    simpa using h
  have hprev := st203_p58
  have hstep := st203_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p60 : ((4715969631867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT203 (i+1))
      = (∑ i ∈ Finset.range 59, stT203 (i+1)) + stT203 60 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 59
    simpa using h
  have hprev := st203_p59
  have hstep := st203_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p61 : ((5207519551851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT203 (i+1))
      = (∑ i ∈ Finset.range 60, stT203 (i+1)) + stT203 61 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 60
    simpa using h
  have hprev := st203_p60
  have hstep := st203_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p62 : ((4661536802037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT203 (i+1))
      = (∑ i ∈ Finset.range 61, stT203 (i+1)) + stT203 62 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 61
    simpa using h
  have hprev := st203_p61
  have hstep := st203_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p63 : ((5234230829159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT203 (i+1))
      = (∑ i ∈ Finset.range 62, stT203 (i+1)) + stT203 63 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 62
    simpa using h
  have hprev := st203_p62
  have hstep := st203_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p64 : ((9304891977463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT203 (i+1))
      = (∑ i ∈ Finset.range 63, stT203 (i+1)) + stT203 64 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 63
    simpa using h
  have hprev := st203_p63
  have hstep := st203_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p65 : ((5230971737339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT203 (i+1))
      = (∑ i ∈ Finset.range 64, stT203 (i+1)) + stT203 65 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 64
    simpa using h
  have hprev := st203_p64
  have hstep := st203_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p66 : ((4666668602909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT203 (i+1))
      = (∑ i ∈ Finset.range 65, stT203 (i+1)) + stT203 66 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 65
    simpa using h
  have hprev := st203_p65
  have hstep := st203_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p67 : ((5202818788361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT203 (i+1))
      = (∑ i ∈ Finset.range 66, stT203 (i+1)) + stT203 67 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 66
    simpa using h
  have hprev := st203_p66
  have hstep := st203_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p68 : ((2357095200427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT203 (i+1))
      = (∑ i ∈ Finset.range 67, stT203 (i+1)) + stT203 68 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 67
    simpa using h
  have hprev := st203_p67
  have hstep := st203_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p69 : ((1282103164409/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT203 (i+1))
      = (∑ i ∈ Finset.range 68, stT203 (i+1)) + stT203 69 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 68
    simpa using h
  have hprev := st203_p68
  have hstep := st203_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p70 : ((1205496156883/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT203 (i+1))
      = (∑ i ∈ Finset.range 69, stT203 (i+1)) + stT203 70 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 69
    simpa using h
  have hprev := st203_p69
  have hstep := st203_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p71 : ((4983779668043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT203 (i+1))
      = (∑ i ∈ Finset.range 70, stT203 (i+1)) + stT203 71 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 70
    simpa using h
  have hprev := st203_p70
  have hstep := st203_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p72 : ((1249791282287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT203 (i+1))
      = (∑ i ∈ Finset.range 71, stT203 (i+1)) + stT203 72 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 71
    simpa using h
  have hprev := st203_p71
  have hstep := st203_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p73 : ((2394381544969/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT203 (i+1))
      = (∑ i ∈ Finset.range 72, stT203 (i+1)) + stT203 73 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 72
    simpa using h
  have hprev := st203_p72
  have hstep := st203_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p74 : ((1295952263183/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT203 (i+1))
      = (∑ i ∈ Finset.range 73, stT203 (i+1)) + stT203 74 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 73
    simpa using h
  have hprev := st203_p73
  have hstep := st203_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p75 : ((9307056413891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT203 (i+1))
      = (∑ i ∈ Finset.range 74, stT203 (i+1)) + stT203 75 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 74
    simpa using h
  have hprev := st203_p74
  have hstep := st203_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p76 : ((2090571772631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT203 (i+1))
      = (∑ i ∈ Finset.range 75, stT203 (i+1)) + stT203 76 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 75
    simpa using h
  have hprev := st203_p75
  have hstep := st203_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p77 : ((9471884878749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT203 (i+1))
      = (∑ i ∈ Finset.range 76, stT203 (i+1)) + stT203 77 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 76
    simpa using h
  have hprev := st203_p76
  have hstep := st203_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p78 : ((10029062538571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT203 (i+1))
      = (∑ i ∈ Finset.range 77, stT203 (i+1)) + stT203 78 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 77
    simpa using h
  have hprev := st203_p77
  have hstep := st203_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p79 : ((2015031920627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT203 (i+1))
      = (∑ i ∈ Finset.range 78, stT203 (i+1)) + stT203 79 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 78
    simpa using h
  have hprev := st203_p78
  have hstep := st203_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p80 : ((9417205538407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT203 (i+1))
      = (∑ i ∈ Finset.range 79, stT203 (i+1)) + stT203 80 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 79
    simpa using h
  have hprev := st203_p79
  have hstep := st203_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p81 : ((5235605494281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT203 (i+1))
      = (∑ i ∈ Finset.range 80, stT203 (i+1)) + stT203 81 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 80
    simpa using h
  have hprev := st203_p80
  have hstep := st203_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p82 : ((4713020524603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT203 (i+1))
      = (∑ i ∈ Finset.range 81, stT203 (i+1)) + stT203 82 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 81
    simpa using h
  have hprev := st203_p81
  have hstep := st203_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p83 : ((156404685617/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT203 (i+1))
      = (∑ i ∈ Finset.range 82, stT203 (i+1)) + stT203 83 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 82
    simpa using h
  have hprev := st203_p82
  have hstep := st203_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p84 : ((5086182606883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT203 (i+1))
      = (∑ i ∈ Finset.range 83, stT203 (i+1)) + stT203 84 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 83
    simpa using h
  have hprev := st203_p83
  have hstep := st203_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p85 : ((1866068299459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT203 (i+1))
      = (∑ i ∈ Finset.range 84, stT203 (i+1)) + stT203 85 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 84
    simpa using h
  have hprev := st203_p84
  have hstep := st203_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p86 : ((5202350666131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT203 (i+1))
      = (∑ i ∈ Finset.range 85, stT203 (i+1)) + stT203 86 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 85
    simpa using h
  have hprev := st203_p85
  have hstep := st203_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p87 : ((9721504827803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT203 (i+1))
      = (∑ i ∈ Finset.range 86, stT203 (i+1)) + stT203 87 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 86
    simpa using h
  have hprev := st203_p86
  have hstep := st203_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p88 : ((9582504302227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT203 (i+1))
      = (∑ i ∈ Finset.range 87, stT203 (i+1)) + stT203 88 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 87
    simpa using h
  have hprev := st203_p87
  have hstep := st203_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p89 : ((10461894773379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT203 (i+1))
      = (∑ i ∈ Finset.range 88, stT203 (i+1)) + stT203 89 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 88
    simpa using h
  have hprev := st203_p88
  have hstep := st203_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p90 : ((9449128543537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT203 (i+1))
      = (∑ i ∈ Finset.range 89, stT203 (i+1)) + stT203 90 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 89
    simpa using h
  have hprev := st203_p89
  have hstep := st203_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p91 : ((9848781577117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT203 (i+1))
      = (∑ i ∈ Finset.range 90, stT203 (i+1)) + stT203 91 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 90
    simpa using h
  have hprev := st203_p90
  have hstep := st203_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p92 : ((2075480205713/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT203 (i+1))
      = (∑ i ∈ Finset.range 91, stT203 (i+1)) + stT203 92 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 91
    simpa using h
  have hprev := st203_p91
  have hstep := st203_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p93 : ((9344784524877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT203 (i+1))
      = (∑ i ∈ Finset.range 92, stT203 (i+1)) + stT203 93 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 92
    simpa using h
  have hprev := st203_p92
  have hstep := st203_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p94 : ((1250393986851/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT203 (i+1))
      = (∑ i ∈ Finset.range 93, stT203 (i+1)) + stT203 94 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 93
    simpa using h
  have hprev := st203_p93
  have hstep := st203_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p95 : ((2576833976051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT203 (i+1))
      = (∑ i ∈ Finset.range 94, stT203 (i+1)) + stT203 95 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 94
    simpa using h
  have hprev := st203_p94
  have hstep := st203_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p96 : ((9319363549373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT203 (i+1))
      = (∑ i ∈ Finset.range 95, stT203 (i+1)) + stT203 96 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 95
    simpa using h
  have hprev := st203_p95
  have hstep := st203_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p97 : ((10038183842149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT203 (i+1))
      = (∑ i ∈ Finset.range 96, stT203 (i+1)) + stT203 97 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 96
    simpa using h
  have hprev := st203_p96
  have hstep := st203_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p98 : ((10310348085357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT203 (i+1))
      = (∑ i ∈ Finset.range 97, stT203 (i+1)) + stT203 98 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 97
    simpa using h
  have hprev := st203_p97
  have hstep := st203_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p99 : ((9328892296989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT203 (i+1))
      = (∑ i ∈ Finset.range 98, stT203 (i+1)) + stT203 99 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 98
    simpa using h
  have hprev := st203_p98
  have hstep := st203_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p100 : ((1245354082881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT203 (i+1))
      = (∑ i ∈ Finset.range 99, stT203 (i+1)) + stT203 100 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 99
    simpa using h
  have hprev := st203_p99
  have hstep := st203_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p101 : ((10382064636999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT203 (i+1))
      = (∑ i ∈ Finset.range 100, stT203 (i+1)) + stT203 101 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 100
    simpa using h
  have hprev := st203_p100
  have hstep := st203_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p102 : ((9391882971967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT203 (i+1))
      = (∑ i ∈ Finset.range 101, stT203 (i+1)) + stT203 102 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 101
    simpa using h
  have hprev := st203_p101
  have hstep := st203_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p103 : ((977912416627/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT203 (i+1))
      = (∑ i ∈ Finset.range 102, stT203 (i+1)) + stT203 103 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 102
    simpa using h
  have hprev := st203_p102
  have hstep := st203_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p104 : ((1046609399977/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT203 (i+1))
      = (∑ i ∈ Finset.range 103, stT203 (i+1)) + stT203 104 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 103
    simpa using h
  have hprev := st203_p103
  have hstep := st203_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p105 : ((1913776955381/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT203 (i+1))
      = (∑ i ∈ Finset.range 104, stT203 (i+1)) + stT203 105 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 104
    simpa using h
  have hprev := st203_p104
  have hstep := st203_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p106 : ((9519243320731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT203 (i+1))
      = (∑ i ∈ Finset.range 105, stT203 (i+1)) + stT203 106 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 105
    simpa using h
  have hprev := st203_p105
  have hstep := st203_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p107 : ((10447137801723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT203 (i+1))
      = (∑ i ∈ Finset.range 106, stT203 (i+1)) + stT203 107 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 106
    simpa using h
  have hprev := st203_p106
  have hstep := st203_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p108 : ((495114938813/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT203 (i+1))
      = (∑ i ∈ Finset.range 107, stT203 (i+1)) + stT203 108 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 107
    simpa using h
  have hprev := st203_p107
  have hstep := st203_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p109 : ((9308370367927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT203 (i+1))
      = (∑ i ∈ Finset.range 108, stT203 (i+1)) + stT203 109 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 108
    simpa using h
  have hprev := st203_p108
  have hstep := st203_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p110 : ((10191746236693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT203 (i+1))
      = (∑ i ∈ Finset.range 109, stT203 (i+1)) + stT203 110 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 109
    simpa using h
  have hprev := st203_p109
  have hstep := st203_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p111 : ((10304707309577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT203 (i+1))
      = (∑ i ∈ Finset.range 110, stT203 (i+1)) + stT203 111 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 110
    simpa using h
  have hprev := st203_p110
  have hstep := st203_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p112 : ((9367780760889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT203 (i+1))
      = (∑ i ∈ Finset.range 111, stT203 (i+1)) + stT203 112 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 111
    simpa using h
  have hprev := st203_p111
  have hstep := st203_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p113 : ((9702780560089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT203 (i+1))
      = (∑ i ∈ Finset.range 112, stT203 (i+1)) + stT203 113 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 112
    simpa using h
  have hprev := st203_p112
  have hstep := st203_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p114 : ((10485169952029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT203 (i+1))
      = (∑ i ∈ Finset.range 113, stT203 (i+1)) + stT203 114 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 113
    simpa using h
  have hprev := st203_p113
  have hstep := st203_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p115 : ((4913314196747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT203 (i+1))
      = (∑ i ∈ Finset.range 114, stT203 (i+1)) + stT203 115 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 114
    simpa using h
  have hprev := st203_p114
  have hstep := st203_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p116 : ((232558817843/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT203 (i+1))
      = (∑ i ∈ Finset.range 115, stT203 (i+1)) + stT203 116 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 115
    simpa using h
  have hprev := st203_p115
  have hstep := st203_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p117 : ((507165975811/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT203 (i+1))
      = (∑ i ∈ Finset.range 116, stT203 (i+1)) + stT203 117 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 116
    simpa using h
  have hprev := st203_p116
  have hstep := st203_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p118 : ((2597509257629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT203 (i+1))
      = (∑ i ∈ Finset.range 117, stT203 (i+1)) + stT203 118 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 117
    simpa using h
  have hprev := st203_p117
  have hstep := st203_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p119 : ((1896184009589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT203 (i+1))
      = (∑ i ∈ Finset.range 118, stT203 (i+1)) + stT203 119 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 118
    simpa using h
  have hprev := st203_p118
  have hstep := st203_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p120 : ((9479848337391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT203 (i+1))
      = (∑ i ∈ Finset.range 119, stT203 (i+1)) + stT203 120 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 119
    simpa using h
  have hprev := st203_p119
  have hstep := st203_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p121 : ((10383121979571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT203 (i+1))
      = (∑ i ∈ Finset.range 120, stT203 (i+1)) + stT203 121 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 120
    simpa using h
  have hprev := st203_p120
  have hstep := st203_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p122 : ((10191928477131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT203 (i+1))
      = (∑ i ∈ Finset.range 121, stT203 (i+1)) + stT203 122 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 121
    simpa using h
  have hprev := st203_p121
  have hstep := st203_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p123 : ((9330241229941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT203 (i+1))
      = (∑ i ∈ Finset.range 122, stT203 (i+1)) + stT203 123 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 122
    simpa using h
  have hprev := st203_p122
  have hstep := st203_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p124 : ((9656626983589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT203 (i+1))
      = (∑ i ∈ Finset.range 123, stT203 (i+1)) + stT203 124 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 123
    simpa using h
  have hprev := st203_p123
  have hstep := st203_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p125 : ((10468927696449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT203 (i+1))
      = (∑ i ∈ Finset.range 124, stT203 (i+1)) + stT203 125 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 124
    simpa using h
  have hprev := st203_p124
  have hstep := st203_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p126 : ((10058676255723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT203 (i+1))
      = (∑ i ∈ Finset.range 125, stT203 (i+1)) + stT203 126 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 125
    simpa using h
  have hprev := st203_p125
  have hstep := st203_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p127 : ((4642629278297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT203 (i+1))
      = (∑ i ∈ Finset.range 126, stT203 (i+1)) + stT203 127 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 126
    simpa using h
  have hprev := st203_p126
  have hstep := st203_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p128 : ((4867478506901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT203 (i+1))
      = (∑ i ∈ Finset.range 127, stT203 (i+1)) + stT203 128 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 127
    simpa using h
  have hprev := st203_p127
  have hstep := st203_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p129 : ((5244403554151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT203 (i+1))
      = (∑ i ∈ Finset.range 128, stT203 (i+1)) + stT203 129 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 128
    simpa using h
  have hprev := st203_p128
  have hstep := st203_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p130 : ((1254768923821/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT203 (i+1))
      = (∑ i ∈ Finset.range 129, stT203 (i+1)) + stT203 130 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 129
    simpa using h
  have hprev := st203_p129
  have hstep := st203_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p131 : ((4640893359739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT203 (i+1))
      = (∑ i ∈ Finset.range 130, stT203 (i+1)) + stT203 131 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 130
    simpa using h
  have hprev := st203_p130
  have hstep := st203_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p132 : ((4848479156963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT203 (i+1))
      = (∑ i ∈ Finset.range 131, stT203 (i+1)) + stT203 132 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 131
    simpa using h
  have hprev := st203_p131
  have hstep := st203_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p133 : ((1309304715629/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT203 (i+1))
      = (∑ i ∈ Finset.range 132, stT203 (i+1)) + stT203 133 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 132
    simpa using h
  have hprev := st203_p132
  have hstep := st203_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p134 : ((10131330554957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT203 (i+1))
      = (∑ i ∈ Finset.range 133, stT203 (i+1)) + stT203 134 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 133
    simpa using h
  have hprev := st203_p133
  have hstep := st203_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p135 : ((9321887331413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT203 (i+1))
      = (∑ i ∈ Finset.range 134, stT203 (i+1)) + stT203 135 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 134
    simpa using h
  have hprev := st203_p134
  have hstep := st203_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p136 : ((9554069582761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT203 (i+1))
      = (∑ i ∈ Finset.range 135, stT203 (i+1)) + stT203 136 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 135
    simpa using h
  have hprev := st203_p135
  have hstep := st203_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p137 : ((2078580924957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT203 (i+1))
      = (∑ i ∈ Finset.range 136, stT203 (i+1)) + stT203 137 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 136
    simpa using h
  have hprev := st203_p136
  have hstep := st203_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p138 : ((2577772791443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT203 (i+1))
      = (∑ i ∈ Finset.range 137, stT203 (i+1)) + stT203 138 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 137
    simpa using h
  have hprev := st203_p137
  have hstep := st203_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p139 : ((9462892835693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT203 (i+1))
      = (∑ i ∈ Finset.range 138, stT203 (i+1)) + stT203 139 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 138
    simpa using h
  have hprev := st203_p138
  have hstep := st203_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p140 : ((2339483892927/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT203 (i+1))
      = (∑ i ∈ Finset.range 139, stT203 (i+1)) + stT203 140 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 139
    simpa using h
  have hprev := st203_p139
  have hstep := st203_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p141 : ((5086888045083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT203 (i+1))
      = (∑ i ∈ Finset.range 140, stT203 (i+1)) + stT203 141 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 140
    simpa using h
  have hprev := st203_p140
  have hstep := st203_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p142 : ((1311265268967/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT203 (i+1))
      = (∑ i ∈ Finset.range 141, stT203 (i+1)) + stT203 142 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 141
    simpa using h
  have hprev := st203_p141
  have hstep := st203_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p143 : ((4884875327151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT203 (i+1))
      = (∑ i ∈ Finset.range 142, stT203 (i+1)) + stT203 143 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 142
    simpa using h
  have hprev := st203_p142
  have hstep := st203_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p144 : ((230998068261/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT203 (i+1))
      = (∑ i ∈ Finset.range 143, stT203 (i+1)) + stT203 144 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 143
    simpa using h
  have hprev := st203_p143
  have hstep := st203_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p145 : ((4892449516473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT203 (i+1))
      = (∑ i ∈ Finset.range 144, stT203 (i+1)) + stT203 145 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 144
    simpa using h
  have hprev := st203_p144
  have hstep := st203_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p146 : ((5247288470643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT203 (i+1))
      = (∑ i ∈ Finset.range 145, stT203 (i+1)) + stT203 146 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 145
    simpa using h
  have hprev := st203_p145
  have hstep := st203_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p147 : ((5103864609639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT203 (i+1))
      = (∑ i ∈ Finset.range 146, stT203 (i+1)) + stT203 147 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 146
    simpa using h
  have hprev := st203_p146
  have hstep := st203_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p148 : ((4698137741579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT203 (i+1))
      = (∑ i ∈ Finset.range 147, stT203 (i+1)) + stT203 148 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 147
    simpa using h
  have hprev := st203_p147
  have hstep := st203_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p149 : ((936090596079/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT203 (i+1))
      = (∑ i ∈ Finset.range 148, stT203 (i+1)) + stT203 149 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 148
    simpa using h
  have hprev := st203_p148
  have hstep := st203_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p150 : ((5075366784219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT203 (i+1))
      = (∑ i ∈ Finset.range 149, stT203 (i+1)) + stT203 150 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 149
    simpa using h
  have hprev := st203_p149
  have hstep := st203_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p151 : ((5262529886339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT203 (i+1))
      = (∑ i ∈ Finset.range 150, stT203 (i+1)) + stT203 151 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 150
    simpa using h
  have hprev := st203_p150
  have hstep := st203_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p152 : ((4954658028333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT203 (i+1))
      = (∑ i ∈ Finset.range 151, stT203 (i+1)) + stT203 152 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 151
    simpa using h
  have hprev := st203_p151
  have hstep := st203_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p153 : ((4626180340621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT203 (i+1))
      = (∑ i ∈ Finset.range 152, stT203 (i+1)) + stT203 153 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 152
    simpa using h
  have hprev := st203_p152
  have hstep := st203_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p154 : ((2386671993141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT203 (i+1))
      = (∑ i ∈ Finset.range 153, stT203 (i+1)) + stT203 154 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 153
    simpa using h
  have hprev := st203_p153
  have hstep := st203_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p155 : ((517218398717/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT203 (i+1))
      = (∑ i ∈ Finset.range 154, stT203 (i+1)) + stT203 155 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 154
    simpa using h
  have hprev := st203_p154
  have hstep := st203_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p156 : ((104625856729/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT203 (i+1))
      = (∑ i ∈ Finset.range 155, stT203 (i+1)) + stT203 156 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 155
    simpa using h
  have hprev := st203_p155
  have hstep := st203_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p157 : ((9734445411841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT203 (i+1))
      = (∑ i ∈ Finset.range 156, stT203 (i+1)) + stT203 157 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 156
    simpa using h
  have hprev := st203_p156
  have hstep := st203_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p158 : ((9219571412053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT203 (i+1))
      = (∑ i ∈ Finset.range 157, stT203 (i+1)) + stT203 158 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 157
    simpa using h
  have hprev := st203_p157
  have hstep := st203_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p159 : ((9652114116269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT203 (i+1))
      = (∑ i ∈ Finset.range 158, stT203 (i+1)) + stT203 159 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 158
    simpa using h
  have hprev := st203_p158
  have hstep := st203_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p160 : ((1301512494313/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT203 (i+1))
      = (∑ i ∈ Finset.range 159, stT203 (i+1)) + stT203 160 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 159
    simpa using h
  have hprev := st203_p159
  have hstep := st203_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p161 : ((5216718228267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT203 (i+1))
      = (∑ i ∈ Finset.range 160, stT203 (i+1)) + stT203 161 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 160
    simpa using h
  have hprev := st203_p160
  have hstep := st203_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p162 : ((4846473598567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT203 (i+1))
      = (∑ i ∈ Finset.range 161, stT203 (i+1)) + stT203 162 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 161
    simpa using h
  have hprev := st203_p161
  have hstep := st203_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p163 : ((9211131242333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT203 (i+1))
      = (∑ i ∈ Finset.range 162, stT203 (i+1)) + stT203 163 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 162
    simpa using h
  have hprev := st203_p162
  have hstep := st203_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p164 : ((9638430020613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT203 (i+1))
      = (∑ i ∈ Finset.range 163, stT203 (i+1)) + stT203 164 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 163
    simpa using h
  have hprev := st203_p163
  have hstep := st203_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p165 : ((10394142941149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT203 (i+1))
      = (∑ i ∈ Finset.range 164, stT203 (i+1)) + stT203 165 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 164
    simpa using h
  have hprev := st203_p164
  have hstep := st203_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p166 : ((10473043245549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT203 (i+1))
      = (∑ i ∈ Finset.range 165, stT203 (i+1)) + stT203 166 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 165
    simpa using h
  have hprev := st203_p165
  have hstep := st203_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p167 : ((1955475712969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT203 (i+1))
      = (∑ i ∈ Finset.range 166, stT203 (i+1)) + stT203 167 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 166
    simpa using h
  have hprev := st203_p166
  have hstep := st203_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p168 : ((460865754331/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT203 (i+1))
      = (∑ i ∈ Finset.range 167, stT203 (i+1)) + stT203 168 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 167
    simpa using h
  have hprev := st203_p167
  have hstep := st203_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p169 : ((190229542003/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT203 (i+1))
      = (∑ i ∈ Finset.range 168, stT203 (i+1)) + stT203 169 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 168
    simpa using h
  have hprev := st203_p168
  have hstep := st203_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p170 : ((5139130048323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT203 (i+1))
      = (∑ i ∈ Finset.range 169, stT203 (i+1)) + stT203 170 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 169
    simpa using h
  have hprev := st203_p169
  have hstep := st203_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p171 : ((10548241845439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT203 (i+1))
      = (∑ i ∈ Finset.range 170, stT203 (i+1)) + stT203 171 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 170
    simpa using h
  have hprev := st203_p170
  have hstep := st203_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p172 : ((79914078017/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT203 (i+1))
      = (∑ i ∈ Finset.range 171, stT203 (i+1)) + stT203 172 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 171
    simpa using h
  have hprev := st203_p171
  have hstep := st203_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p173 : ((9297770511693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT203 (i+1))
      = (∑ i ∈ Finset.range 172, stT203 (i+1)) + stT203 173 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 172
    simpa using h
  have hprev := st203_p172
  have hstep := st203_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p174 : ((1863797783323/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT203 (i+1))
      = (∑ i ∈ Finset.range 173, stT203 (i+1)) + stT203 174 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 173
    simpa using h
  have hprev := st203_p173
  have hstep := st203_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p175 : ((10021116764927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT203 (i+1))
      = (∑ i ∈ Finset.range 174, stT203 (i+1)) + stT203 175 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 174
    simpa using h
  have hprev := st203_p174
  have hstep := st203_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p176 : ((10558393893989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT203 (i+1))
      = (∑ i ∈ Finset.range 175, stT203 (i+1)) + stT203 176 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 175
    simpa using h
  have hprev := st203_p175
  have hstep := st203_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p177 : ((2059187961541/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT203 (i+1))
      = (∑ i ∈ Finset.range 176, stT203 (i+1)) + stT203 177 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 176
    simpa using h
  have hprev := st203_p176
  have hstep := st203_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p178 : ((9548232168593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT203 (i+1))
      = (∑ i ∈ Finset.range 177, stT203 (i+1)) + stT203 178 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 177
    simpa using h
  have hprev := st203_p177
  have hstep := st203_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p179 : ((9187213853669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT203 (i+1))
      = (∑ i ∈ Finset.range 178, stT203 (i+1)) + stT203 179 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 178
    simpa using h
  have hprev := st203_p178
  have hstep := st203_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p180 : ((2406104743021/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT203 (i+1))
      = (∑ i ∈ Finset.range 179, stT203 (i+1)) + stT203 180 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 179
    simpa using h
  have hprev := st203_p179
  have hstep := st203_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p181 : ((2588891887031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT203 (i+1))
      = (∑ i ∈ Finset.range 180, stT203 (i+1)) + stT203 181 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 180
    simpa using h
  have hprev := st203_p180
  have hstep := st203_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p182 : ((105543883199/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT203 (i+1))
      = (∑ i ∈ Finset.range 181, stT203 (i+1)) + stT203 182 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 181
    simpa using h
  have hprev := st203_p181
  have hstep := st203_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p183 : ((1000353117383/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT203 (i+1))
      = (∑ i ∈ Finset.range 182, stT203 (i+1)) + stT203 183 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 182
    simpa using h
  have hprev := st203_p182
  have hstep := st203_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p184 : ((931784183189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT203 (i+1))
      = (∑ i ∈ Finset.range 183, stT203 (i+1)) + stT203 184 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 183
    simpa using h
  have hprev := st203_p183
  have hstep := st203_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p185 : ((184971456309/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT203 (i+1))
      = (∑ i ∈ Finset.range 184, stT203 (i+1)) + stT203 185 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 184
    simpa using h
  have hprev := st203_p184
  have hstep := st203_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p186 : ((394621696307/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT203 (i+1))
      = (∑ i ∈ Finset.range 185, stT203 (i+1)) + stT203 186 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 185
    simpa using h
  have hprev := st203_p185
  have hstep := st203_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p187 : ((10500946111019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT203 (i+1))
      = (∑ i ∈ Finset.range 186, stT203 (i+1)) + stT203 187 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 186
    simpa using h
  have hprev := st203_p186
  have hstep := st203_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p188 : ((5239669928947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT203 (i+1))
      = (∑ i ∈ Finset.range 187, stT203 (i+1)) + stT203 188 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 187
    simpa using h
  have hprev := st203_p187
  have hstep := st203_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p189 : ((2457227350413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT203 (i+1))
      = (∑ i ∈ Finset.range 188, stT203 (i+1)) + stT203 189 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 188
    simpa using h
  have hprev := st203_p188
  have hstep := st203_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p190 : ((4616486061909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT203 (i+1))
      = (∑ i ∈ Finset.range 189, stT203 (i+1)) + stT203 190 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 189
    simpa using h
  have hprev := st203_p189
  have hstep := st203_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p191 : ((4653227702481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT203 (i+1))
      = (∑ i ∈ Finset.range 190, stT203 (i+1)) + stT203 191 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 190
    simpa using h
  have hprev := st203_p190
  have hstep := st203_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p192 : ((9968589515409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT203 (i+1))
      = (∑ i ∈ Finset.range 191, stT203 (i+1)) + stT203 192 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 191
    simpa using h
  have hprev := st203_p191
  have hstep := st203_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p193 : ((10543508635169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT203 (i+1))
      = (∑ i ∈ Finset.range 192, stT203 (i+1)) + stT203 193 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 192
    simpa using h
  have hprev := st203_p192
  have hstep := st203_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p194 : ((418190296617/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT203 (i+1))
      = (∑ i ∈ Finset.range 193, stT203 (i+1)) + stT203 194 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 193
    simpa using h
  have hprev := st203_p193
  have hstep := st203_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p195 : ((979603401987/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT203 (i+1))
      = (∑ i ∈ Finset.range 194, stT203 (i+1)) + stT203 195 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 194
    simpa using h
  have hprev := st203_p194
  have hstep := st203_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p196 : ((1152626634447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT203 (i+1))
      = (∑ i ∈ Finset.range 195, stT203 (i+1)) + stT203 196 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 195
    simpa using h
  have hprev := st203_p195
  have hstep := st203_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p197 : ((4645147897893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT203 (i+1))
      = (∑ i ∈ Finset.range 196, stT203 (i+1)) + stT203 197 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 196
    simpa using h
  have hprev := st203_p196
  have hstep := st203_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p198 : ((496578256263/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT203 (i+1))
      = (∑ i ∈ Finset.range 197, stT203 (i+1)) + stT203 198 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 197
    simpa using h
  have hprev := st203_p197
  have hstep := st203_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p199 : ((5262788815129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT203 (i+1))
      = (∑ i ∈ Finset.range 198, stT203 (i+1)) + stT203 199 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 198
    simpa using h
  have hprev := st203_p198
  have hstep := st203_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p200 : ((10508633225217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT203 (i+1))
      = (∑ i ∈ Finset.range 199, stT203 (i+1)) + stT203 200 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 199
    simpa using h
  have hprev := st203_p199
  have hstep := st203_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p201 : ((9901594823967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT203 (i+1))
      = (∑ i ∈ Finset.range 200, stT203 (i+1)) + stT203 201 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 200
    simpa using h
  have hprev := st203_p200
  have hstep := st203_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p202 : ((9275222333251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT203 (i+1))
      = (∑ i ∈ Finset.range 201, stT203 (i+1)) + stT203 202 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 201
    simpa using h
  have hprev := st203_p201
  have hstep := st203_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p203 : ((9208406379377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT203 (i+1))
      = (∑ i ∈ Finset.range 202, stT203 (i+1)) + stT203 203 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 202
    simpa using h
  have hprev := st203_p202
  have hstep := st203_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p204 : ((9757788033737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT203 (i+1))
      = (∑ i ∈ Finset.range 203, stT203 (i+1)) + stT203 204 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 203
    simpa using h
  have hprev := st203_p203
  have hstep := st203_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p205 : ((10419815862137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT203 (i+1))
      = (∑ i ∈ Finset.range 204, stT203 (i+1)) + stT203 205 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 204
    simpa using h
  have hprev := st203_p204
  have hstep := st203_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p206 : ((2649527981759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT203 (i+1))
      = (∑ i ∈ Finset.range 205, stT203 (i+1)) + stT203 206 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 205
    simpa using h
  have hprev := st203_p205
  have hstep := st203_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p207 : ((10137574544783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT203 (i+1))
      = (∑ i ∈ Finset.range 206, stT203 (i+1)) + stT203 207 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 206
    simpa using h
  have hprev := st203_p206
  have hstep := st203_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p208 : ((9450171979023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT203 (i+1))
      = (∑ i ∈ Finset.range 207, stT203 (i+1)) + stT203 208 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 207
    simpa using h
  have hprev := st203_p207
  have hstep := st203_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p209 : ((4569844737919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT203 (i+1))
      = (∑ i ∈ Finset.range 208, stT203 (i+1)) + stT203 209 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 208
    simpa using h
  have hprev := st203_p208
  have hstep := st203_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p210 : ((2368159044357/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT203 (i+1))
      = (∑ i ∈ Finset.range 209, stT203 (i+1)) + stT203 210 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 209
    simpa using h
  have hprev := st203_p209
  have hstep := st203_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p211 : ((1269673754649/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT203 (i+1))
      = (∑ i ∈ Finset.range 210, stT203 (i+1)) + stT203 211 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 210
    simpa using h
  have hprev := st203_p210
  have hstep := st203_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p212 : ((5303524117509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT203 (i+1))
      = (∑ i ∈ Finset.range 211, stT203 (i+1)) + stT203 212 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 211
    simpa using h
  have hprev := st203_p211
  have hstep := st203_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p213 : ((5221596068779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT203 (i+1))
      = (∑ i ∈ Finset.range 212, stT203 (i+1)) + stT203 213 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 212
    simpa using h
  have hprev := st203_p212
  have hstep := st203_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p214 : ((2451991265489/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT203 (i+1))
      = (∑ i ∈ Finset.range 213, stT203 (i+1)) + stT203 214 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 213
    simpa using h
  have hprev := st203_p213
  have hstep := st203_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p215 : ((9232968939501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT203 (i+1))
      = (∑ i ∈ Finset.range 214, stT203 (i+1)) + stT203 215 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 214
    simpa using h
  have hprev := st203_p214
  have hstep := st203_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p216 : ((9191492943303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT203 (i+1))
      = (∑ i ∈ Finset.range 215, stT203 (i+1)) + stT203 216 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 215
    simpa using h
  have hprev := st203_p215
  have hstep := st203_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p217 : ((9713236828291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT203 (i+1))
      = (∑ i ∈ Finset.range 216, stT203 (i+1)) + stT203 217 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 216
    simpa using h
  have hprev := st203_p216
  have hstep := st203_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p218 : ((5185599782263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT203 (i+1))
      = (∑ i ∈ Finset.range 217, stT203 (i+1)) + stT203 218 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 217
    simpa using h
  have hprev := st203_p217
  have hstep := st203_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p219 : ((2127172689621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT203 (i+1))
      = (∑ i ∈ Finset.range 218, stT203 (i+1)) + stT203 219 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 218
    simpa using h
  have hprev := st203_p218
  have hstep := st203_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p220 : ((2059894136781/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT203 (i+1))
      = (∑ i ∈ Finset.range 219, stT203 (i+1)) + stT203 220 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 219
    simpa using h
  have hprev := st203_p219
  have hstep := st203_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p221 : ((9632251716589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT203 (i+1))
      = (∑ i ∈ Finset.range 220, stT203 (i+1)) + stT203 221 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 220
    simpa using h
  have hprev := st203_p220
  have hstep := st203_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p222 : ((4579590332363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT203 (i+1))
      = (∑ i ∈ Finset.range 221, stT203 (i+1)) + stT203 222 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 221
    simpa using h
  have hprev := st203_p221
  have hstep := st203_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p223 : ((4623047873867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT203 (i+1))
      = (∑ i ∈ Finset.range 222, stT203 (i+1)) + stT203 223 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 222
    simpa using h
  have hprev := st203_p222
  have hstep := st203_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p224 : ((2455442422751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT203 (i+1))
      = (∑ i ∈ Finset.range 223, stT203 (i+1)) + stT203 224 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 223
    simpa using h
  have hprev := st203_p223
  have hstep := st203_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p225 : ((1305352300411/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT203 (i+1))
      = (∑ i ∈ Finset.range 224, stT203 (i+1)) + stT203 225 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 224
    simpa using h
  have hprev := st203_p224
  have hstep := st203_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p226 : ((2659625001587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT203 (i+1))
      = (∑ i ∈ Finset.range 225, stT203 (i+1)) + stT203 226 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 225
    simpa using h
  have hprev := st203_p225
  have hstep := st203_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p227 : ((2566252309267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT203 (i+1))
      = (∑ i ∈ Finset.range 226, stT203 (i+1)) + stT203 227 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 226
    simpa using h
  have hprev := st203_p226
  have hstep := st203_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p228 : ((9604874074541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT203 (i+1))
      = (∑ i ∈ Finset.range 227, stT203 (i+1)) + stT203 228 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 227
    simpa using h
  have hprev := st203_p227
  have hstep := st203_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p229 : ((1829605486399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT203 (i+1))
      = (∑ i ∈ Finset.range 228, stT203 (i+1)) + stT203 229 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 228
    simpa using h
  have hprev := st203_p228
  have hstep := st203_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p230 : ((1845551932319/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT203 (i+1))
      = (∑ i ∈ Finset.range 229, stT203 (i+1)) + stT203 230 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 229
    simpa using h
  have hprev := st203_p229
  have hstep := st203_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p231 : ((391282808803/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT203 (i+1))
      = (∑ i ∈ Finset.range 230, stT203 (i+1)) + stT203 231 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 230
    simpa using h
  have hprev := st203_p230
  have hstep := st203_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p232 : ((10407665119171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT203 (i+1))
      = (∑ i ∈ Finset.range 231, stT203 (i+1)) + stT203 232 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 231
    simpa using h
  have hprev := st203_p231
  have hstep := st203_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p233 : ((2131295228849/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT203 (i+1))
      = (∑ i ∈ Finset.range 232, stT203 (i+1)) + stT203 233 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 232
    simpa using h
  have hprev := st203_p232
  have hstep := st203_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p234 : ((10354708071109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT203 (i+1))
      = (∑ i ∈ Finset.range 233, stT203 (i+1)) + stT203 234 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 233
    simpa using h
  have hprev := st203_p233
  have hstep := st203_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p235 : ((4859420949041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT203 (i+1))
      = (∑ i ∈ Finset.range 234, stT203 (i+1)) + stT203 235 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 234
    simpa using h
  have hprev := st203_p234
  have hstep := st203_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p236 : ((2298846119083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT203 (i+1))
      = (∑ i ∈ Finset.range 235, stT203 (i+1)) + stT203 236 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 235
    simpa using h
  have hprev := st203_p235
  have hstep := st203_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p237 : ((4573075808661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT203 (i+1))
      = (∑ i ∈ Finset.range 236, stT203 (i+1)) + stT203 237 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 236
    simpa using h
  have hprev := st203_p236
  have hstep := st203_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p238 : ((1200185875037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT203 (i+1))
      = (∑ i ∈ Finset.range 237, stT203 (i+1)) + stT203 238 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 237
    simpa using h
  have hprev := st203_p237
  have hstep := st203_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p239 : ((512358239821/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT203 (i+1))
      = (∑ i ∈ Finset.range 238, stT203 (i+1)) + stT203 239 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 238
    simpa using h
  have hprev := st203_p238
  have hstep := st203_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p240 : ((10644889709461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT203 (i+1))
      = (∑ i ∈ Finset.range 239, stT203 (i+1)) + stT203 240 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 239
    simpa using h
  have hprev := st203_p239
  have hstep := st203_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p241 : ((5264715826469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT203 (i+1))
      = (∑ i ∈ Finset.range 240, stT203 (i+1)) + stT203 241 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 240
    simpa using h
  have hprev := st203_p240
  have hstep := st203_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p242 : ((9981393127663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT203 (i+1))
      = (∑ i ∈ Finset.range 241, stT203 (i+1)) + stT203 242 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 241
    simpa using h
  have hprev := st203_p241
  have hstep := st203_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p243 : ((292690926001/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT203 (i+1))
      = (∑ i ∈ Finset.range 242, stT203 (i+1)) + stT203 243 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 242
    simpa using h
  have hprev := st203_p242
  have hstep := st203_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p244 : ((4543793452411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT203 (i+1))
      = (∑ i ∈ Finset.range 243, stT203 (i+1)) + stT203 244 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 243
    simpa using h
  have hprev := st203_p243
  have hstep := st203_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p245 : ((4662323797253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT203 (i+1))
      = (∑ i ∈ Finset.range 244, stT203 (i+1)) + stT203 245 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 244
    simpa using h
  have hprev := st203_p244
  have hstep := st203_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p246 : ((4960242659621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT203 (i+1))
      = (∑ i ∈ Finset.range 245, stT203 (i+1)) + stT203 246 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 245
    simpa using h
  have hprev := st203_p245
  have hstep := st203_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p247 : ((5245323024839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT203 (i+1))
      = (∑ i ∈ Finset.range 246, stT203 (i+1)) + stT203 247 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 246
    simpa using h
  have hprev := st203_p246
  have hstep := st203_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p248 : ((5336330589839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT203 (i+1))
      = (∑ i ∈ Finset.range 247, stT203 (i+1)) + stT203 248 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 247
    simpa using h
  have hprev := st203_p247
  have hstep := st203_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p249 : ((5177190835289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT203 (i+1))
      = (∑ i ∈ Finset.range 248, stT203 (i+1)) + stT203 249 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 248
    simpa using h
  have hprev := st203_p248
  have hstep := st203_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_p250 : ((4869348569393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT203 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT203 (i+1))
      = (∑ i ∈ Finset.range 249, stT203 (i+1)) + stT203 250 := by
    have h := Finset.sum_range_succ (fun i => stT203 (i+1)) 249
    simpa using h
  have hprev := st203_p249
  have hstep := st203_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st203_s250 :
    |Real.sin (((203 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))
      - ((114489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 7276413/10000000) (δ := 10179/1000000000) (ψ := -460977/1000000) 203 178
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 203`** (evaluated boundary). -/
theorem station_203_sign : 0 < hardyG ((((203:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 203 250 (by norm_num) (by norm_num)
    ((-460977/1000000 : ℚ) : ℝ)
  have hchain := st203_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT203 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((203 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-460977/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st203_c250
  have hsinb := abs_le.mp st203_s250
  have hbdy_lo : ((-3637095788601/206046250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((203 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ))) / 2
          - ((((203:ℕ)):ℝ))
            * Real.sin (((203 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-460977/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((203:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((203:ℝ) * Real.log (250:ℝ) - ((-460977/1000000 : ℚ) : ℝ))) / 2
        - ((203:ℝ)) * Real.sin ((203:ℝ) * Real.log (250:ℝ) - ((-460977/1000000 : ℚ) : ℝ))
        ≥ ((-46005993/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((203:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-46005993/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-46005993/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-46005993/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((203:ℕ)):ℝ))+1) * (((((203:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((28704885187/31250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((4869348569393/5000000000000 : ℚ) : ℝ) + ((-3637095788601/206046250000000 : ℚ) : ℝ)
      - ((28704885187/31250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-460977/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((203:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-460977/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((203:ℕ)):ℝ)))).re
      - Real.sin ((-460977/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((203:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((203:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((203:ℕ)):ℝ))
      = (((((203:ℕ)):ℝ)) * (Real.log ((((203:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((203:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_203
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
  have hθwin : |(((-460977/1000000 : ℚ) : ℝ) + ((40:ℤ)) * (2*Real.pi)) - theta ((((203:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((203:ℕ)):ℝ)))
    (φ := ((-460977/1000000 : ℚ) : ℝ) + ((40:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-460977/1000000 : ℚ)) : ℝ) 40).1,
    (cos_sin_shift (((-460977/1000000 : ℚ)) : ℝ) 40).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_203_sign
end AxiomAudit
