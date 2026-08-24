import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 142` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT142 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((142 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-100181/125000 : ℚ) : ℝ))

theorem st142_c1 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((695667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100181/500000) (δ := 1/1000000000) (ψ := -100181/125000) 142 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t1 : ((695617/1000000 : ℚ) : ℝ) ≤ stT142 1 := by
  have hc : ((695617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((695617/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((695617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c2 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((66243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1628277/5000000) (δ := 1779/250000000) (ψ := -100181/125000) 142 16
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t2 : ((936640605887/5000000000000 : ℚ) : ℝ) ≤ stT142 2 := by
  have hc : ((132461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((936640605887/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((132461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c3 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((962359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -688113/10000000) (δ := 3561/500000000) (ψ := -100181/125000) 142 25
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t3 : ((2777946468059/5000000000000 : ℚ) : ℝ) ≤ stT142 3 := by
  have hc : ((962309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2777946468059/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((962309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c4 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-965069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7191253/10000000) (δ := 1781/250000000) (ψ := -100181/125000) 142 31
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t4 : ((-4825595965119/10000000000000 : ℚ) : ℝ) ≤ stT142 4 := by
  have hc : ((-965119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4825595965119/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-965119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c5 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-499993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7840549/10000000) (δ := 1809/250000000) (ψ := -100181/125000) 142 37
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t5 : ((-139759281153/312500000000 : ℚ) : ℝ) ≤ stT142 5 := by
  have hc : ((-250009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139759281153/312500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-250009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c6 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-36163/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5948269/10000000) (δ := 1799/250000000) (ψ := -100181/125000) 142 41
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t6 : ((-295290077873/1000000000000 : ℚ) : ℝ) ≤ stT142 6 := by
  have hc : ((-72331/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295290077873/1000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-72331/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c7 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((24677/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1651339/10000000) (δ := 3643/500000000) (ψ := -100181/125000) 142 44
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t7 : ((373057477177/1250000000000 : ℚ) : ℝ) ≤ stT142 7 := by
  have hc : ((394807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373057477177/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((394807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c8 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((716211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1931097/10000000) (δ := 7239/1000000000) (ψ := -100181/125000) 142 47
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t8 : ((2532010848813/10000000000000 : ℚ) : ℝ) ≤ stT142 8 := by
  have hc : ((716161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2532010848813/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((716161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c9 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((108561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -844957/2500000) (δ := 179/25000000) (ψ := -100181/125000) 142 50
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t9 : ((45223328811/625000000000 : ℚ) : ℝ) ≤ stT142 9 := by
  have hc : ((13567/62500 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45223328811/625000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((13567/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c10 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((251863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2607223/10000000) (δ := 287/40000000) (ψ := -100181/125000) 142 52
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t10 : ((398190757563/2500000000000 : ℚ) : ℝ) ≤ stT142 10 := by
  have hc : ((125919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((398190757563/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((125919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c11 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-106433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5026417/10000000) (δ := 3607/500000000) (ψ := -100181/125000) 142 54
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t11 : ((-320945317287/2500000000000 : ℚ) : ℝ) ≤ stT142 11 := by
  have hc : ((-212891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320945317287/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-212891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c12 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-113511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2249769/5000000) (δ := 1801/250000000) (ψ := -100181/125000) 142 56
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t12 : ((-80017157/1220703125 : ℚ) : ℝ) ≤ stT142 12 := by
  have hc : ((-3548/15625 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80017157/1220703125 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-3548/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c13 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((825613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149877/1000000) (δ := 3609/500000000) (ψ := -100181/125000) 142 58
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t13 : ((4579397961/20000000000 : ℚ) : ℝ) ≤ stT142 13 := by
  have hc : ((825563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4579397961/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((825563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c14 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((63463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3608817/10000000) (δ := 7171/1000000000) (ψ := -100181/125000) 142 60
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t14 : ((21193145007/625000000000 : ℚ) : ℝ) ≤ stT142 14 := by
  have hc : ((31719/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21193145007/625000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((31719/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c15 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-119743/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5175699/10000000) (δ := 227/31250000) (ψ := -100181/125000) 142 61
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t15 : ((-618414767379/5000000000000 : ℚ) : ℝ) ≤ stT142 15 := by
  have hc : ((-239511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618414767379/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-239511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c16 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((236899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166453/500000) (δ := 7249/1000000000) (ψ := -100181/125000) 142 63
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t16 : ((236849/4000000 : ℚ) : ℝ) ≤ stT142 16 := by
  have hc : ((236849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236849/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((236849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c17 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((545439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248471/1000000) (δ := 3571/500000000) (ψ := -100181/125000) 142 64
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t17 : ((330690620871/2500000000000 : ℚ) : ℝ) ≤ stT142 17 := by
  have hc : ((545389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330690620871/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((545389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c18 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-475491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7067979/10000000) (δ := 14/1953125) (ψ := -100181/125000) 142 65
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t18 : ((-280200537217/1250000000000 : ℚ) : ℝ) ≤ stT142 18 := by
  have hc : ((-118879/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280200537217/1250000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-118879/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c19 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-471367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1288523/2500000) (δ := 361/50000000) (ψ := -100181/125000) 142 67
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t19 : ((-540752540943/5000000000000 : ℚ) : ℝ) ≤ stT142 19 := by
  have hc : ((-471417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-540752540943/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-471417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c20 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((60981/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2652933/10000000) (δ := 729/100000000) (ψ := -100181/125000) 142 68
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t20 : ((545374505233/5000000000000 : ℚ) : ℝ) ≤ stT142 20 := by
  have hc : ((243899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((545374505233/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((243899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c21 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((228663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130047/1250000) (δ := 3603/500000000) (ψ := -100181/125000) 142 69
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t21 : ((498956090789/2500000000000 : ℚ) : ℝ) ≤ stT142 21 := by
  have hc : ((457301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498956090789/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((457301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c22 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((62227/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233739/10000000) (δ := 111/15625000) (ψ := -100181/125000) 142 70
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t22 : ((1061293896537/5000000000000 : ℚ) : ℝ) ≤ stT142 22 := by
  have hc : ((497791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1061293896537/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((497791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c23 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((997919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161313/10000000) (δ := 7211/1000000000) (ψ := -100181/125000) 142 71
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t23 : ((260087569767/1250000000000 : ℚ) : ℝ) ≤ stT142 23 := by
  have hc : ((997869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260087569767/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((997869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c24 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((954073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760619/10000000) (δ := 1457/200000000) (ψ := -100181/125000) 142 72
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t24 : ((1947390862543/10000000000000 : ℚ) : ℝ) ≤ stT142 24 := by
  have hc : ((954023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1947390862543/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((954023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c25 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((351671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -494193/2500000) (δ := 7177/1000000000) (ψ := -100181/125000) 142 73
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t25 : ((175823/1250000 : ℚ) : ℝ) ≤ stT142 25 := by
  have hc : ((175823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175823/1250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((175823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c26 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((66193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3761387/10000000) (δ := 727/100000000) (ψ := -100181/125000) 142 74
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t26 : ((129717072023/10000000000000 : ℚ) : ℝ) ≤ stT142 26 := by
  have hc : ((66143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129717072023/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((66143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c27 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-756419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6071543/10000000) (δ := 181/25000000) (ψ := -100181/125000) 142 75
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t27 : ((-1455825346969/10000000000000 : ℚ) : ℝ) ≤ stT142 27 := by
  have hc : ((-756469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1455825346969/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-756469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c28 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-918709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 683899/1000000) (δ := 7163/1000000000) (ψ := -100181/125000) 142 75
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t28 : ((-1736291889657/10000000000000 : ℚ) : ℝ) ≤ stT142 28 := by
  have hc : ((-918759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1736291889657/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-918759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c29 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((4219/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1794219/5000000) (δ := 907/125000000) (ψ := -100181/125000) 142 76
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t29 : ((125305331487/5000000000000 : ℚ) : ℝ) ≤ stT142 29 := by
  have hc : ((67479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125305331487/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((67479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c30 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((999429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21123/2500000) (δ := 3627/500000000) (ψ := -100181/125000) 142 77
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t30 : ((1824607214839/10000000000000 : ℚ) : ℝ) ≤ stT142 30 := by
  have hc : ((999379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1824607214839/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((999379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c31 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-89899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4152041/10000000) (δ := 3581/500000000) (ψ := -100181/125000) 142 78
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t31 : ((-80776630623/5000000000000 : ℚ) : ℝ) ≤ stT142 31 := by
  have hc : ((-89949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80776630623/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-89949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c32 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-191413/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7118747/10000000) (δ := 7241/1000000000) (ψ := -100181/125000) 142 78
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t32 : ((-338391262441/2000000000000 : ℚ) : ℝ) ≤ stT142 32 := by
  have hc : ((-191423/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338391262441/2000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-191423/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c33 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((594719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1167351/5000000) (δ := 3567/500000000) (ψ := -100181/125000) 142 79
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t33 : ((129398190393/1250000000000 : ℚ) : ℝ) ≤ stT142 33 := by
  have hc : ((594669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129398190393/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((594669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c34 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((222251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1387723/5000000) (δ := 897/125000000) (ψ := -100181/125000) 142 80
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t34 : ((38111425661/500000000000 : ℚ) : ℝ) ≤ stT142 34 := by
  have hc : ((111113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38111425661/500000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((111113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c35 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-247707/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1878779/2500000) (δ := 7227/1000000000) (ψ := -100181/125000) 142 80
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t35 : ((-837445000651/5000000000000 : ℚ) : ℝ) ≤ stT142 35 := by
  have hc : ((-495439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-837445000651/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-495439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c36 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((749739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1807823/10000000) (δ := 7283/1000000000) (ψ := -100181/125000) 142 81
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t36 : ((624740583437/5000000000000 : ℚ) : ℝ) ≤ stT142 36 := by
  have hc : ((749689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((624740583437/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((749689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c37 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-49221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -521687/1250000) (δ := 7213/1000000000) (ψ := -100181/125000) 142 82
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t37 : ((-4047996577/250000000000 : ℚ) : ℝ) ≤ stT142 37 := by
  have hc : ((-24623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4047996577/250000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-24623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c38 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-259931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1058743/2000000) (δ := 7213/1000000000) (ψ := -100181/125000) 142 82
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t38 : ((-21085226127/250000000000 : ℚ) : ℝ) ≤ stT142 38 := by
  have hc : ((-64989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21085226127/250000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-64989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c39 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((177659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238589/2000000) (δ := 7297/1000000000) (ψ := -100181/125000) 142 83
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t39 : ((284465968369/2000000000000 : ℚ) : ℝ) ≤ stT142 39 := by
  have hc : ((177649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284465968369/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((177649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c40 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-999721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3897437/5000000) (δ := 7297/1000000000) (ψ := -100181/125000) 142 83
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t40 : ((-1580776919169/10000000000000 : ℚ) : ℝ) ≤ stT142 40 := by
  have hc : ((-999771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1580776919169/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-999771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c41 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((942383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 852783/10000000) (δ := 3599/500000000) (ψ := -100181/125000) 142 84
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t41 : ((1471676312421/10000000000000 : ℚ) : ℝ) ≤ stT142 41 := by
  have hc : ((942333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1471676312421/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((942333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c42 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-203269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1575133/2500000) (δ := 889/125000000) (ψ := -100181/125000) 142 85
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t42 : ((-313670266071/2500000000000 : ℚ) : ℝ) ≤ stT142 42 := by
  have hc : ((-406563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313670266071/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-406563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c43 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((681403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410559/2000000) (δ := 7291/1000000000) (ψ := -100181/125000) 142 85
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t43 : ((207810620941/2000000000000 : ℚ) : ℝ) ≤ stT142 43 := by
  have hc : ((681353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207810620941/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((681353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c44 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-23461/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1098779/2000000) (δ := 7219/1000000000) (ψ := -100181/125000) 142 86
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t44 : ((-35371809891/400000000000 : ℚ) : ℝ) ≤ stT142 44 := by
  have hc : ((-23463/40000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35371809891/400000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-23463/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c45 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((272847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2483949/10000000) (δ := 7219/1000000000) (ψ := -100181/125000) 142 86
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t45 : ((203349378221/2500000000000 : ℚ) : ℝ) ≤ stT142 45 := by
  have hc : ((136411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203349378221/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((136411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c46 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-56283/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1084301/2000000) (δ := 3563/500000000) (ψ := -100181/125000) 142 87
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t46 : ((-129675239/1562500000 : ℚ) : ℝ) ≤ stT142 46 := by
  have hc : ((-1759/3125 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129675239/1562500000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-1759/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c47 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((633063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2213231/10000000) (δ := 7277/1000000000) (ψ := -100181/125000) 142 87
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t47 : ((923343779437/10000000000000 : ℚ) : ℝ) ≤ stT142 47 := by
  have hc : ((633013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((923343779437/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((633013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c48 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-742981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -240831/400000) (δ := 717/100000000) (ψ := -100181/125000) 142 88
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t48 : ((-67029569541/625000000000 : ℚ) : ℝ) ≤ stT142 48 := by
  have hc : ((-743031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67029569541/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-743031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c49 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((86801/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1299041/10000000) (δ := 717/100000000) (ψ := -100181/125000) 142 88
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t49 : ((30998562129/250000000000 : ℚ) : ℝ) ≤ stT142 49 := by
  have hc : ((21699/25000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30998562129/250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((21699/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c50 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-484847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113077/156250) (δ := 357/50000000) (ψ := -100181/125000) 142 89
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t50 : ((-42857048163/312500000000 : ℚ) : ℝ) ≤ stT142 50 := by
  have hc : ((-60609/62500 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42857048163/312500000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-60609/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c51 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((498287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41401/2000000) (δ := 357/50000000) (ψ := -100181/125000) 142 89
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t51 : ((8721328917/62500000000 : ℚ) : ℝ) ≤ stT142 51 := by
  have hc : ((249131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8721328917/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((249131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c52 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-55807/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 334321/500000) (δ := 7263/1000000000) (ψ := -100181/125000) 142 89
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t52 : ((-619157973231/5000000000000 : ℚ) : ℝ) ≤ stT142 52 := by
  have hc : ((-446481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619157973231/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-446481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c53 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((12373/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -282429/1250000) (δ := 1431/200000000) (ψ := -100181/125000) 142 90
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t53 : ((849712053/10000000000 : ℚ) : ℝ) ≤ stT142 53 := by
  have hc : ((3093/5000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((849712053/10000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((3093/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c54 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-22343/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 547033/1250000) (δ := 453/62500000) (ψ := -100181/125000) 142 90
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t54 : ((-30413485179/1250000000000 : ℚ) : ℝ) ≤ stT142 54 := by
  have hc : ((-89397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30413485179/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-89397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c55 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-17441/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4817769/10000000) (δ := 1431/200000000) (ψ := -100181/125000) 142 91
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t55 : ((-117604077/2500000000 : ℚ) : ℝ) ≤ stT142 55 := by
  have hc : ((-34887/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117604077/2500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-34887/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c56 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((201783/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 789399/5000000) (δ := 453/62500000) (ψ := -100181/125000) 142 91
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t56 : ((269627129773/2500000000000 : ℚ) : ℝ) ≤ stT142 56 := by
  have hc : ((403541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269627129773/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((403541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c57 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-199999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7845807/10000000) (δ := 7141/1000000000) (ψ := -100181/125000) 142 92
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t57 : ((-264918520797/2000000000000 : ℚ) : ℝ) ≤ stT142 57 := by
  have hc : ((-200009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264918520797/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-200009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c58 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((196159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -835859/5000000) (δ := 7141/1000000000) (ψ := -100181/125000) 142 92
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t58 : ((64388226969/625000000000 : ℚ) : ℝ) ≤ stT142 58 := by
  have hc : ((392293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64388226969/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((392293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c59 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-186817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2198397/5000000) (δ := 7141/1000000000) (ψ := -100181/125000) 142 92
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t59 : ((-24328027863/1000000000000 : ℚ) : ℝ) ≤ stT142 59 := by
  have hc : ((-186867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24328027863/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-186867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c60 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-537157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5344649/10000000) (δ := 3617/500000000) (ψ := -100181/125000) 142 93
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t60 : ((-138706310193/2000000000000 : ℚ) : ℝ) ≤ stT142 60 := by
  have hc : ((-537207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138706310193/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-537207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c61 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((15284/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 523253/10000000) (δ := 7169/1000000000) (ψ := -100181/125000) 142 93
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t61 : ((39136288449/312500000000 : ℚ) : ℝ) ≤ stT142 61 := by
  have hc : ((489063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39136288449/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((489063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c62 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-202989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 629573/1000000) (δ := 3617/500000000) (ψ := -100181/125000) 142 93
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t62 : ((-257812311003/2500000000000 : ℚ) : ℝ) ≤ stT142 62 := by
  have hc : ((-406003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257812311003/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-406003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c63 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((77881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3732091/10000000) (δ := 7127/1000000000) (ψ := -100181/125000) 142 94
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t63 : ((98057798111/10000000000000 : ℚ) : ℝ) ≤ stT142 63 := by
  have hc : ((77831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98057798111/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((77831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c64 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((736157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464639/2500000) (δ := 1819/250000000) (ψ := -100181/125000) 142 94
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t64 : ((736107/8000000 : ℚ) : ℝ) ≤ stT142 64 := by
  have hc : ((736107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((736107/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((736107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c65 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-980741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7362547/10000000) (δ := 1819/250000000) (ψ := -100181/125000) 142 94
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t65 : ((-304130538817/2500000000000 : ℚ) : ℝ) ≤ stT142 65 := by
  have hc : ((-980791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304130538817/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-980791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c66 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((12187/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1462727/5000000) (δ := 449/62500000) (ψ := -100181/125000) 142 95
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t66 : ((119993804919/2500000000000 : ℚ) : ℝ) ≤ stT142 66 := by
  have hc : ((194967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119993804919/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((194967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c67 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((142313/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2413/10000) (δ := 7219/1000000000) (ψ := -100181/125000) 142 95
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t67 : ((173847667047/2500000000000 : ℚ) : ℝ) ≤ stT142 67 := by
  have hc : ((284601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173847667047/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((284601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c68 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-498681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7672361/10000000) (δ := 449/62500000) (ψ := -100181/125000) 142 95
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t68 : ((-302385146687/2500000000000 : ℚ) : ℝ) ≤ stT142 68 := by
  have hc : ((-249353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302385146687/2500000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-249353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c69 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((208247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -713257/2500000) (δ := 7291/1000000000) (ψ := -100181/125000) 142 96
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t69 : ((62667430119/1250000000000 : ℚ) : ℝ) ≤ stT142 69 := by
  have hc : ((104111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62667430119/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((104111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c70 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((124011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28187/125000) (δ := 889/125000000) (ψ := -100181/125000) 142 96
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t70 : ((37052366807/500000000000 : ℚ) : ℝ) ≤ stT142 70 := by
  have hc : ((124001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37052366807/500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((124001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c71 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-487353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7290493/10000000) (δ := 889/125000000) (ψ := -100181/125000) 142 96
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t71 : ((-144602859399/1250000000000 : ℚ) : ℝ) ≤ stT142 71 := by
  have hc : ((-243689/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144602859399/1250000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-243689/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c72 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((47181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1726167/5000000) (δ := 1441/200000000) (ψ := -100181/125000) 142 97
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t72 : ((111177192207/5000000000000 : ℚ) : ℝ) ≤ stT142 72 := by
  have hc : ((94337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111177192207/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((94337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c73 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((837713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22567/156250) (δ := 3599/500000000) (ψ := -100181/125000) 142 97
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t73 : ((980409989493/10000000000000 : ℚ) : ℝ) ≤ stT142 73 := by
  have hc : ((837663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((980409989493/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((837663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c74 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-806917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1568569/2500000) (δ := 3599/500000000) (ψ := -100181/125000) 142 97
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t74 : ((-938080577259/10000000000000 : ℚ) : ℝ) ≤ stT142 74 := by
  have hc : ((-806967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-938080577259/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-806967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c75 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-292269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4668487/10000000) (δ := 1421/200000000) (ψ := -100181/125000) 142 98
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t75 : ((-337541041619/10000000000000 : ℚ) : ℝ) ≤ stT142 75 := by
  have hc : ((-292319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337541041619/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-292319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c76 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((99991/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33559/10000000) (δ := 1421/200000000) (ψ := -100181/125000) 142 98
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t76 : ((28672935227/250000000000 : ℚ) : ℝ) ≤ stT142 76 := by
  have hc : ((49993/50000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28672935227/250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((49993/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c77 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-73609/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2337077/5000000) (δ := 3649/500000000) (ψ := -100181/125000) 142 98
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t77 : ((-83899503129/2500000000000 : ℚ) : ℝ) ≤ stT142 77 := by
  have hc : ((-147243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83899503129/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-147243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c78 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-211767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3226551/5000000) (δ := 7191/1000000000) (ψ := -100181/125000) 142 99
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t78 : ((-239793268701/2500000000000 : ℚ) : ℝ) ≤ stT142 78 := by
  have hc : ((-423559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239793268701/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-423559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c79 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((358153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1930757/10000000) (δ := 7191/1000000000) (ψ := -100181/125000) 142 99
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t79 : ((25182822321/312500000000 : ℚ) : ℝ) ≤ stT142 79 := by
  have hc : ((22383/31250 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25182822321/312500000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((22383/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c80 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((105713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2534717/10000000) (δ := 7191/1000000000) (ψ := -100181/125000) 142 99
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t80 : ((118179442199/2000000000000 : ℚ) : ℝ) ≤ stT142 80 := by
  have hc : ((105703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118179442199/2000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((105703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c81 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-934583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1388941/2000000) (δ := 1803/250000000) (ψ := -100181/125000) 142 99
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t81 : ((-129810242737/1250000000000 : ℚ) : ℝ) ≤ stT142 81 := by
  have hc : ((-934633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129810242737/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-934633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c82 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-190973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4407373/10000000) (δ := 7119/1000000000) (ψ := -100181/125000) 142 100
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t82 : ((-52737438817/2500000000000 : ℚ) : ℝ) ≤ stT142 82 := by
  have hc : ((-191023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52737438817/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-191023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c83 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((99913/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26069/2500000) (δ := 7119/1000000000) (ψ := -100181/125000) 142 100
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t83 : ((13707902117/125000000000 : ℚ) : ℝ) ≤ stT142 83 := by
  have hc : ((24977/25000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13707902117/125000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((24977/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c84 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-87993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4147257/10000000) (δ := 3571/250000000) (ψ := -100181/125000) 142 100
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t84 : ((-9606283687/1000000000000 : ℚ) : ℝ) ≤ stT142 84 := by
  have hc : ((-88043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9606283687/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-88043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c85 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-980501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1839869/2500000) (δ := 7227/1000000000) (ψ := -100181/125000) 142 101
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t85 : ((-1063557583803/10000000000000 : ℚ) : ℝ) ≤ stT142 85 := by
  have hc : ((-980551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1063557583803/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-980551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c86 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((7097/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -801849/2500000) (δ := 7227/1000000000) (ψ := -100181/125000) 142 101
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t86 : ((30606155241/1000000000000 : ℚ) : ℝ) ≤ stT142 86 := by
  have hc : ((28383/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30606155241/1000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((28383/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c87 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((468179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 896723/10000000) (δ := 897/125000000) (ψ := -100181/125000) 142 101
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t87 : ((15684797539/156250000000 : ℚ) : ℝ) ≤ stT142 87 := by
  have hc : ((234077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15684797539/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((234077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c88 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-199657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 619239/1250000) (δ := 7227/1000000000) (ψ := -100181/125000) 142 101
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t88 : ((-26607726341/625000000000 : ℚ) : ℝ) ≤ stT142 88 := by
  have hc : ((-99841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26607726341/625000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-99841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c89 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-36113/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6742729/10000000) (δ := 3567/500000000) (ψ := -100181/125000) 142 102
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t89 : ((-3828182777/40000000000 : ℚ) : ℝ) ≤ stT142 89 := by
  have hc : ((-7223/8000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3828182777/40000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-7223/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c90 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((444229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -173513/625000) (δ := 7269/1000000000) (ψ := -100181/125000) 142 102
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t90 : ((117051382617/2500000000000 : ℚ) : ℝ) ≤ stT142 90 := by
  have hc : ((444179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117051382617/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((444179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c91 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((35867/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1146489/10000000) (δ := 14269/1000000000) (ψ := -100181/125000) 142 102
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t91 : ((1879835283/20000000000 : ℚ) : ℝ) ≤ stT142 91 := by
  have hc : ((7173/8000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1879835283/20000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((7173/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c92 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-42569/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2513151/5000000) (δ := 3567/500000000) (ψ := -100181/125000) 142 102
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t92 : ((-22193251451/500000000000 : ℚ) : ℝ) ≤ stT142 92 := by
  have hc : ((-21287/50000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22193251451/500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-21287/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c93 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-459733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -427737/625000) (δ := 3581/500000000) (ψ := -100181/125000) 142 103
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t93 : ((-29796686101/312500000000 : ℚ) : ℝ) ≤ stT142 93 := by
  have hc : ((-229879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29796686101/312500000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-229879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c94 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((344787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38087/125000) (δ := 7241/1000000000) (ψ := -100181/125000) 142 103
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t94 : ((355568981277/10000000000000 : ℚ) : ℝ) ≤ stT142 94 := by
  have hc : ((344737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355568981277/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((344737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c95 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((479989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141937/2000000) (δ := 3581/500000000) (ψ := -100181/125000) 142 103
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t95 : ((61554063099/625000000000 : ℚ) : ℝ) ≤ stT142 95 := by
  have hc : ((119991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61554063099/625000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((119991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c96 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-12417/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4426997/10000000) (δ := 7241/1000000000) (ψ := -100181/125000) 142 103
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t96 : ((-101409923181/5000000000000 : ℚ) : ℝ) ≤ stT142 96 := by
  have hc : ((-99361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101409923181/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-99361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c97 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-248733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7602173/10000000) (δ := 1451/200000000) (ψ := -100181/125000) 142 104
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t97 : ((-505125994377/5000000000000 : ℚ) : ℝ) ≤ stT142 97 := by
  have hc : ((-497491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505125994377/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-497491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c98 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-13649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -792223/2000000) (δ := 1787/250000000) (ψ := -100181/125000) 142 104
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t98 : ((-13838085947/10000000000000 : ℚ) : ℝ) ≤ stT142 98 := by
  have hc : ((-13699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13838085947/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-13699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c99 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((989821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -357013/10000000) (δ := 1787/250000000) (ψ := -100181/125000) 142 104
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t99 : ((994756476527/10000000000000 : ℚ) : ℝ) ≤ stT142 99 := by
  have hc : ((989771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((994756476527/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((989771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c100 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((282557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3210843/10000000) (δ := 1451/200000000) (ψ := -100181/125000) 142 104
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t100 : ((282506717493/10000000000000 : ℚ) : ℝ) ≤ stT142 100 := by
  have hc : ((282507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282506717493/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((282507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c101 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-14108/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1348647/2000000) (δ := 1451/200000000) (ψ := -100181/125000) 142 104
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t101 : ((-224620375639/2500000000000 : ℚ) : ℝ) ≤ stT142 101 := by
  have hc : ((-451481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224620375639/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-451481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c102 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-577831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5467161/10000000) (δ := 1451/200000000) (ψ := -100181/125000) 142 105
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t102 : ((-143046929097/2500000000000 : ℚ) : ℝ) ≤ stT142 102 := by
  have hc : ((-577881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143046929097/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-577881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c103 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((695631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1001873/5000000) (δ := 1787/250000000) (ψ := -100181/125000) 142 105
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t103 : ((685376131149/10000000000000 : ℚ) : ℝ) ≤ stT142 103 := by
  have hc : ((695581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((685376131149/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((695581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c104 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((210409/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1426229/10000000) (δ := 1451/200000000) (ψ := -100181/125000) 142 105
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t104 : ((20631059997/250000000000 : ℚ) : ℝ) ≤ stT142 104 := by
  have hc : ((420793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20631059997/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((420793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c105 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-35093/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4823401/10000000) (δ := 1787/250000000) (ψ := -100181/125000) 142 105
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t105 : ((-17126086649/500000000000 : ℚ) : ℝ) ≤ stT142 105 := by
  have hc : ((-17549/50000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17126086649/500000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-17549/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c106 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-99107/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -939953/1250000) (δ := 181/25000000) (ψ := -100181/125000) 142 106
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t106 : ((-6016631127/62500000000 : ℚ) : ℝ) ≤ stT142 106 := by
  have hc : ((-12389/12500 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6016631127/62500000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-12389/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c107 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-25879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837249/2000000) (δ := 181/25000000) (ψ := -100181/125000) 142 106
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t107 : ((-50060542071/5000000000000 : ℚ) : ℝ) ≤ stT142 107 := by
  have hc : ((-51783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50060542071/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-51783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c108 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((938147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -883893/10000000) (δ := 181/25000000) (ψ := -100181/125000) 142 106
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t108 : ((3610735353/40000000000 : ℚ) : ℝ) ≤ stT142 108 := by
  have hc : ((938097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3610735353/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((938097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c109 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((115489/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 597/2500) (δ := 181/25000000) (ψ := -100181/125000) 142 106
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t109 : ((55304394327/1000000000000 : ℚ) : ℝ) ≤ stT142 109 := by
  have hc : ((115479/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55304394327/1000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((115479/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c110 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-31487/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2815019/5000000) (δ := 7163/1000000000) (ψ := -100181/125000) 142 106
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t110 : ((-60048146277/1000000000000 : ℚ) : ℝ) ≤ stT142 110 := by
  have hc : ((-62979/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60048146277/1000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-62979/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c111 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-922801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6865211/10000000) (δ := 7133/1000000000) (ψ := -100181/125000) 142 107
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t111 : ((-437965704729/5000000000000 : ℚ) : ℝ) ≤ stT142 111 := by
  have hc : ((-922851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437965704729/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-922851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c112 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((19619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1840679/5000000) (δ := 7133/1000000000) (ψ := -100181/125000) 142 107
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t112 : ((18528759799/2000000000000 : ℚ) : ℝ) ≤ stT142 112 := by
  have hc : ((19609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18528759799/2000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((19609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c113 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((977967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -525763/10000000) (δ := 7133/1000000000) (ψ := -100181/125000) 142 107
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t113 : ((11499326003/125000000000 : ℚ) : ℝ) ≤ stT142 113 := by
  have hc : ((977917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11499326003/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((977917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c114 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((50553/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1301/5000) (δ := 7133/1000000000) (ψ := -100181/125000) 142 107
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t114 : ((2367124929/50000000000 : ℚ) : ℝ) ≤ stT142 114 := by
  have hc : ((12637/25000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2367124929/50000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((12637/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c115 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-651977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89101/156250) (δ := 727/100000000) (ψ := -100181/125000) 142 107
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t115 : ((-121603687527/2000000000000 : ℚ) : ℝ) ≤ stT142 115 := by
  have hc : ((-652027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121603687527/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-652027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c116 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-3731/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -693191/1000000) (δ := 3613/500000000) (ψ := -100181/125000) 142 108
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t116 : ((-541302091/6250000000 : ℚ) : ℝ) ≤ stT142 116 := by
  have hc : ((-583/625 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-541302091/6250000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-583/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c117 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((16931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3884661/10000000) (δ := 3613/500000000) (ψ := -100181/125000) 142 108
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t117 : ((31212969/20000000000 : ℚ) : ℝ) ≤ stT142 117 := by
  have hc : ((16881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31212969/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((16881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c118 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((940959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -431681/5000000) (δ := 7177/1000000000) (ψ := -100181/125000) 142 108
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t118 : ((433088180883/5000000000000 : ℚ) : ℝ) ≤ stT142 118 := by
  have hc : ((940909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433088180883/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((940909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c119 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((657753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 533103/2500000) (δ := 7177/1000000000) (ψ := -100181/125000) 142 108
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t119 : ((301457512347/5000000000000 : ℚ) : ℝ) ≤ stT142 119 := by
  have hc : ((657703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301457512347/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((657703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c120 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-226651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2551579/5000000) (δ := 3613/500000000) (ψ := -100181/125000) 142 108
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t120 : ((-51731486699/1250000000000 : ℚ) : ℝ) ≤ stT142 120 := by
  have hc : ((-56669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51731486699/1250000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-56669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c121 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-124619/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7658731/10000000) (δ := 7119/1000000000) (ψ := -100181/125000) 142 109
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t121 : ((-453182772591/5000000000000 : ℚ) : ℝ) ≤ stT142 121 := by
  have hc : ((-498501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453182772591/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-498501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c122 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-39791/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4736903/10000000) (δ := 1821/250000000) (ψ := -100181/125000) 142 109
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t122 : ((-72061517331/2500000000000 : ℚ) : ℝ) ≤ stT142 122 := by
  have hc : ((-159189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72061517331/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-159189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c123 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((741447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -459733/2500000) (δ := 7119/1000000000) (ψ := -100181/125000) 142 109
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t123 : ((668494691593/10000000000000 : ℚ) : ℝ) ≤ stT142 123 := by
  have hc : ((741397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((668494691593/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((741397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c124 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((915427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 517787/5000000) (δ := 7119/1000000000) (ψ := -100181/125000) 142 109
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t124 : ((411016172901/5000000000000 : ℚ) : ℝ) ≤ stT142 124 := by
  have hc : ((915377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411016172901/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((915377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c125 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((7997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 777401/2000000) (δ := 7119/1000000000) (ψ := -100181/125000) 142 109
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t125 : ((1782593011/1250000000000 : ℚ) : ℝ) ≤ stT142 125 := by
  have hc : ((1993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1782593011/1250000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((1993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c126 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-449063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1678929/2500000) (δ := 7119/1000000000) (ψ := -100181/125000) 142 109
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t126 : ((-6251241807/78125000000 : ℚ) : ℝ) ≤ stT142 126 := by
  have hc : ((-14034/15625 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6251241807/78125000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-14034/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c127 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-392773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6185937/10000000) (δ := 1803/250000000) (ψ := -100181/125000) 142 110
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t127 : ((-174276027443/2500000000000 : ℚ) : ℝ) ≤ stT142 127 := by
  have hc : ((-196399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174276027443/2500000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-196399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c128 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((52153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3401601/10000000) (δ := 1803/250000000) (ψ := -100181/125000) 142 110
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t128 : ((92172203123/5000000000000 : ℚ) : ℝ) ≤ stT142 128 := by
  have hc : ((104281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92172203123/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((104281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c129 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((6047/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15973/250000) (δ := 1803/250000000) (ψ := -100181/125000) 142 110
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t129 : ((1703617923/20000000000 : ℚ) : ℝ) ≤ stT142 129 := by
  have hc : ((96747/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1703617923/20000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((96747/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c130 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((666751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210239/1000000) (δ := 1803/250000000) (ψ := -100181/125000) 142 110
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t130 : ((292367722829/5000000000000 : ℚ) : ℝ) ≤ stT142 130 := by
  have hc : ((666701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292367722829/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((666701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c131 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-14027/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15071/31250) (δ := 7191/1000000000) (ψ := -100181/125000) 142 110
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t131 : ((-2451441489/80000000000 : ℚ) : ℝ) ≤ stT142 131 := by
  have hc : ((-14029/40000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2451441489/80000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-14029/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c132 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-198243/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7522353/10000000) (δ := 7191/1000000000) (ψ := -100181/125000) 142 110
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t132 : ((-172557230417/2000000000000 : ℚ) : ℝ) ≤ stT142 132 := by
  have hc : ((-198253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172557230417/2000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-198253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c133 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-295277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2753177/5000000) (δ := 3649/500000000) (ψ := -100181/125000) 142 111
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t133 : ((-12802965861/250000000000 : ℚ) : ℝ) ≤ stT142 133 := by
  have hc : ((-147651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12802965861/250000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-147651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c134 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((418621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1423587/5000000) (δ := 2861/200000000) (ψ := -100181/125000) 142 111
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t134 : ((90397523157/2500000000000 : ℚ) : ℝ) ≤ stT142 134 := by
  have hc : ((418571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90397523157/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((418571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c135 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((996549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -103883/5000000) (δ := 3649/500000000) (ψ := -100181/125000) 142 111
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t135 : ((428824411169/5000000000000 : ℚ) : ℝ) ≤ stT142 135 := by
  have hc : ((996499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428824411169/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((996499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c136 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((284763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2412169/10000000) (δ := 1421/200000000) (ψ := -100181/125000) 142 111
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t136 : ((30520069637/625000000000 : ℚ) : ℝ) ≤ stT142 136 := by
  have hc : ((142369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30520069637/625000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((142369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c137 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-210423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1002587/2000000) (δ := 3649/500000000) (ψ := -100181/125000) 142 111
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t137 : ((-5618685387/156250000000 : ℚ) : ℝ) ≤ stT142 137 := by
  have hc : ((-13153/31250 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5618685387/156250000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-13153/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c138 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-248657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7594743/10000000) (δ := 1421/200000000) (ψ := -100181/125000) 142 111
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t138 : ((-423363305123/5000000000000 : ℚ) : ℝ) ≤ stT142 138 := by
  have hc : ((-497339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-423363305123/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-497339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c139 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-604557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2775007/5000000) (δ := 7197/1000000000) (ψ := -100181/125000) 142 112
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t139 : ((-512821006723/10000000000000 : ℚ) : ℝ) ≤ stT142 139 := by
  have hc : ((-604607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512821006723/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-604607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c140 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((18021/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -751299/2500000) (δ := 3603/500000000) (ψ := -100181/125000) 142 112
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t140 : ((15228407349/500000000000 : ℚ) : ℝ) ≤ stT142 140 := by
  have hc : ((36037/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15228407349/500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((36037/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c141 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((981737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478519/10000000) (δ := 3603/500000000) (ψ := -100181/125000) 142 112
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t141 : ((826728688737/10000000000000 : ℚ) : ℝ) ≤ stT142 141 := by
  have hc : ((981687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((826728688737/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((981687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c142 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((687951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2030337/10000000) (δ := 3603/500000000) (ψ := -100181/125000) 142 112
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t142 : ((577273449081/10000000000000 : ℚ) : ℝ) ≤ stT142 142 := by
  have hc : ((687901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((577273449081/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((687901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c143 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-117801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904317/2000000) (δ := 3603/500000000) (ψ := -100181/125000) 142 112
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t143 : ((-49265583859/2500000000000 : ℚ) : ℝ) ≤ stT142 143 := by
  have hc : ((-58913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49265583859/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-58913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c144 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-941609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3497719/5000000) (δ := 3603/500000000) (ψ := -100181/125000) 142 112
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t144 : ((-392358230553/5000000000000 : ℚ) : ℝ) ≤ stT142 144 := by
  have hc : ((-941659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-392358230553/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-941659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c145 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-401259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563937/2500000) (δ := 7113/1000000000) (ψ := -100181/125000) 142 113
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t145 : ((-16662415211/250000000000 : ℚ) : ℝ) ≤ stT142 145 := by
  have hc : ((-100321/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16662415211/250000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-100321/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c146 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((22217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3815869/10000000) (δ := 729/100000000) (ψ := -100181/125000) 142 113
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t146 : ((229577627/62500000000 : ℚ) : ℝ) ≤ stT142 146 := by
  have hc : ((1387/31250 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229577627/62500000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((1387/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c147 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((106101/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -696337/5000000) (δ := 7113/1000000000) (ψ := -100181/125000) 142 113
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t147 : ((175010928947/2500000000000 : ℚ) : ℝ) ≤ stT142 147 := by
  have hc : ((424379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175010928947/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((424379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c148 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((918847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1014119/10000000) (δ := 729/100000000) (ψ := -100181/125000) 142 113
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t148 : ((377622810609/5000000000000 : ℚ) : ℝ) ≤ stT142 148 := by
  have hc : ((918797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((377622810609/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((918797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c149 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((20739/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136189/400000) (δ := 7113/1000000000) (ψ := -100181/125000) 142 113
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t149 : ((8492967777/500000000000 : ℚ) : ℝ) ≤ stT142 149 := by
  have hc : ((10367/50000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8492967777/500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((10367/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c150 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-134993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1444821/2500000) (δ := 729/100000000) (ψ := -100181/125000) 142 113
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t150 : ((-110229544491/2000000000000 : ℚ) : ℝ) ≤ stT142 150 := by
  have hc : ((-135003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110229544491/2000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-135003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c151 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-248387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3784923/5000000) (δ := 7183/1000000000) (ψ := -100181/125000) 142 114
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t151 : ((-404289561411/5000000000000 : ℚ) : ℝ) ≤ stT142 151 := by
  have hc : ((-496799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404289561411/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-496799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c152 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-496743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5226597/10000000) (δ := 361/50000000) (ψ := -100181/125000) 142 114
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t152 : ((-100738194161/2500000000000 : ℚ) : ℝ) ≤ stT142 152 := by
  have hc : ((-496793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100738194161/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-496793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c153 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((399809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18117/62500) (δ := 361/50000000) (ψ := -100181/125000) 142 114
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t153 : ((80796490767/2500000000000 : ℚ) : ℝ) ≤ stT142 153 := by
  have hc : ((399759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80796490767/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((399759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c154 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((486327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293001/5000000) (δ := 7183/1000000000) (ψ := -100181/125000) 142 114
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t154 : ((97968212561/1250000000000 : ℚ) : ℝ) ≤ stT142 154 := by
  have hc : ((243151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97968212561/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((243151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c155 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((193653/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213967/1250000) (δ := 361/50000000) (ψ := -100181/125000) 142 114
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t155 : ((311071457539/5000000000000 : ℚ) : ℝ) ≤ stT142 155 := by
  have hc : ((387281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311071457539/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((387281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c156 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-13541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 798941/2000000) (δ := 7183/1000000000) (ψ := -100181/125000) 142 114
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t156 : ((-5430747903/2500000000000 : ℚ) : ℝ) ≤ stT142 156 := by
  have hc : ((-6783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5430747903/2500000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-6783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c157 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-160853/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1565771/2500000) (δ := 7183/1000000000) (ψ := -100181/125000) 142 114
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t157 : ((-128382669081/2000000000000 : ℚ) : ℝ) ≤ stT142 157 := by
  have hc : ((-160863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128382669081/2000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-160863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c158 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-965033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7190913/10000000) (δ := 7127/1000000000) (ψ := -100181/125000) 142 115
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t158 : ((-383889750657/5000000000000 : ℚ) : ℝ) ≤ stT142 158 := by
  have hc : ((-965083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383889750657/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-965083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c159 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-3983/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4951147/10000000) (δ := 7127/1000000000) (ψ := -100181/125000) 142 115
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t159 : ((-1579561321/50000000000 : ℚ) : ℝ) ≤ stT142 159 := by
  have hc : ((-7967/20000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1579561321/50000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-7967/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c160 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((46233/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2725439/10000000) (δ := 7127/1000000000) (ψ := -100181/125000) 142 115
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t160 : ((9136605933/250000000000 : ℚ) : ℝ) ≤ stT142 160 := by
  have hc : ((11557/25000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9136605933/250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((11557/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c161 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((97897/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128403/2500000) (δ := 1819/250000000) (ψ := -100181/125000) 142 115
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t161 : ((1928741603/25000000000 : ℚ) : ℝ) ≤ stT142 161 := by
  have hc : ((24473/25000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1928741603/25000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((24473/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c162 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((195361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 421137/2500000) (δ := 1819/250000000) (ψ := -100181/125000) 142 115
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t162 : ((153480237389/2500000000000 : ℚ) : ℝ) ≤ stT142 162 := by
  have hc : ((390697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153480237389/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((390697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c163 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((23121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3869183/10000000) (δ := 7127/1000000000) (ψ := -100181/125000) 142 115
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t163 : ((903529573/500000000000 : ℚ) : ℝ) ≤ stT142 163 := by
  have hc : ((23071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((903529573/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((23071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c164 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-748221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3020217/5000000) (δ := 7127/1000000000) (ψ := -100181/125000) 142 115
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t164 : ((-584301627499/10000000000000 : ℚ) : ℝ) ≤ stT142 164 := by
  have hc : ((-748271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-584301627499/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-748271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c165 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-990521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1877371/2500000) (δ := 3617/500000000) (ψ := -100181/125000) 142 116
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t165 : ((-771158532929/10000000000000 : ℚ) : ℝ) ≤ stT142 165 := by
  have hc : ((-990571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-771158532929/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-990571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c166 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-543827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1341117/2500000) (δ := 7169/1000000000) (ψ := -100181/125000) 142 116
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t166 : ((-422130677427/10000000000000 : ℚ) : ℝ) ≤ stT142 166 := by
  have hc : ((-543877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422130677427/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-543877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c167 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((274313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1616151/5000000) (δ := 3617/500000000) (ψ := -100181/125000) 142 116
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t167 : ((212231017449/10000000000000 : ℚ) : ℝ) ≤ stT142 167 := by
  have hc : ((274263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212231017449/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((274263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c168 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((902539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1112917/10000000) (δ := 7169/1000000000) (ψ := -100181/125000) 142 116
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t168 : ((174071175831/2500000000000 : ℚ) : ℝ) ≤ stT142 168 := by
  have hc : ((902489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174071175831/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((902489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c169 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((922003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 993937/10000000) (δ := 7169/1000000000) (ψ := -100181/125000) 142 116
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t169 : ((70919390619/1000000000000 : ℚ) : ℝ) ≤ stT142 169 := by
  have hc : ((921953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70919390619/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((921953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c170 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((329207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3088331/10000000) (δ := 3617/500000000) (ψ := -100181/125000) 142 116
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t170 : ((63112892337/2500000000000 : ℚ) : ℝ) ≤ stT142 170 := by
  have hc : ((329157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63112892337/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((329157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c171 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-3817/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5170441/10000000) (δ := 7169/1000000000) (ψ := -100181/125000) 142 116
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t171 : ((-182452633/5000000000 : ℚ) : ℝ) ≤ stT142 171 := by
  have hc : ((-19087/40000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182452633/5000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-19087/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c172 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-970033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7240411/10000000) (δ := 3617/500000000) (ψ := -100181/125000) 142 116
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t172 : ((-739681496919/10000000000000 : ℚ) : ℝ) ≤ stT142 172 := by
  have hc : ((-970083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-739681496919/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-970083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c173 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-104711/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3204791/5000000) (δ := 3571/500000000) (ψ := -100181/125000) 142 117
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t173 : ((-159230118267/2500000000000 : ℚ) : ℝ) ≤ stT142 173 := by
  have hc : ((-418869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159230118267/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-418869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c174 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-86853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4363469/10000000) (δ := 7261/1000000000) (ψ := -100181/125000) 142 117
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t174 : ((-32931062461/2500000000000 : ℚ) : ℝ) ≤ stT142 174 := by
  have hc : ((-43439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32931062461/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-43439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c175 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((37283/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232907/1000000) (δ := 3571/500000000) (ψ := -100181/125000) 142 117
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t175 : ((28180901349/625000000000 : ℚ) : ℝ) ≤ stT142 175 := by
  have hc : ((298239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28180901349/625000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((298239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c176 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((198501/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7657/250000) (δ := 3571/500000000) (ψ := -100181/125000) 142 117
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t176 : ((74809074499/1000000000000 : ℚ) : ℝ) ≤ stT142 176 := by
  have hc : ((198491/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74809074499/1000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((198491/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c177 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((388147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1705079/10000000) (δ := 3571/500000000) (ψ := -100181/125000) 142 117
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t177 : ((72932587203/1250000000000 : ℚ) : ℝ) ≤ stT142 177 := by
  have hc : ((194061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72932587203/1250000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((194061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c178 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((88649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1852539/5000000) (δ := 3571/500000000) (ψ := -100181/125000) 142 117
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t178 : ((66407697069/10000000000000 : ℚ) : ℝ) ≤ stT142 178 := by
  have hc : ((88599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66407697069/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((88599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c179 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-324687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2846947/5000000) (δ := 7261/1000000000) (ψ := -100181/125000) 142 117
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t179 : ((-7584419951/156250000000 : ℚ) : ℝ) ≤ stT142 179 := by
  have hc : ((-40589/62500 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7584419951/156250000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-40589/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c180 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-49867/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7671599/10000000) (δ := 7261/1000000000) (ψ := -100181/125000) 142 117
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t180 : ((-18585265521/250000000000 : ℚ) : ℝ) ≤ stT142 180 := by
  have hc : ((-99739/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18585265521/250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-99739/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c181 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-755909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6069593/10000000) (δ := 3577/500000000) (ψ := -100181/125000) 142 118
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t181 : ((-112380108981/2000000000000 : ℚ) : ℝ) ≤ stT142 181 := by
  have hc : ((-755959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112380108981/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-755959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c182 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-4663/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -822737/2000000) (δ := 3577/500000000) (ψ := -100181/125000) 142 118
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t182 : ((-22136097/4000000000 : ℚ) : ℝ) ≤ stT142 182 := by
  have hc : ((-37329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22136097/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-37329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c183 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((646823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1084231/5000000) (δ := 7249/1000000000) (ψ := -100181/125000) 142 118
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t183 : ((478108183833/10000000000000 : ℚ) : ℝ) ≤ stT142 183 := by
  have hc : ((646773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478108183833/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((646773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c184 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((248907/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116927/5000000) (δ := 7249/1000000000) (ψ := -100181/125000) 142 118
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t184 : ((366974530901/5000000000000 : ℚ) : ℝ) ≤ stT142 184 := by
  have hc : ((497789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366974530901/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((497789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c185 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((780011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1690281/10000000) (δ := 3577/500000000) (ψ := -100181/125000) 142 118
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t185 : ((286719123327/5000000000000 : ℚ) : ℝ) ≤ stT142 185 := by
  have hc : ((779961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286719123327/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((779961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c186 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((128831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720803/2000000) (δ := 3577/500000000) (ψ := -100181/125000) 142 118
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t186 : ((18885347307/2000000000000 : ℚ) : ℝ) ≤ stT142 186 := by
  have hc : ((128781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18885347307/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((128781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c187 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-147733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220301/400000) (δ := 3577/500000000) (ψ := -100181/125000) 142 118
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t187 : ((-216084590043/5000000000000 : ℚ) : ℝ) ≤ stT142 187 := by
  have hc : ((-295491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216084590043/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-295491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c188 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-491809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7400847/10000000) (δ := 7249/1000000000) (ψ := -100181/125000) 142 118
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t188 : ((-7174136641/100000000000 : ℚ) : ℝ) ≤ stT142 188 := by
  have hc : ((-245917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7174136641/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-245917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c189 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-420391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3211903/5000000) (δ := 1789/250000000) (ψ := -100181/125000) 142 119
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t189 : ((-4778244617/78125000000 : ℚ) : ℝ) ≤ stT142 189 := by
  have hc : ((-13138/15625 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4778244617/78125000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-13138/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c190 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-49363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4550471/10000000) (δ := 1789/250000000) (ψ := -100181/125000) 142 119
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t190 : ((-35818975921/2000000000000 : ℚ) : ℝ) ≤ stT142 190 := by
  have hc : ((-49373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35818975921/2000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-49373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c191 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((475931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1343467/5000000) (δ := 1789/250000000) (ψ := -100181/125000) 142 119
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t191 : ((172167559347/5000000000000 : ℚ) : ℝ) ≤ stT142 191 := by
  have hc : ((475881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172167559347/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((475881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c192 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((47249/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20829/250000) (δ := 7247/1000000000) (ψ := -100181/125000) 142 119
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t192 : ((68194369691/1000000000000 : ℚ) : ℝ) ≤ stT142 192 := by
  have hc : ((94493/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68194369691/1000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((94493/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c193 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((45967/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 505497/5000000) (δ := 7247/1000000000) (ψ := -100181/125000) 142 119
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t193 : ((13234374627/200000000000 : ℚ) : ℝ) ≤ stT142 193 := by
  have hc : ((91929/100000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13234374627/200000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((91929/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c194 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((419181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1422817/5000000) (δ := 7247/1000000000) (ψ := -100181/125000) 142 119
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t194 : ((150459227249/5000000000000 : ℚ) : ℝ) ≤ stT142 194 := by
  have hc : ((419131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150459227249/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((419131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c195 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-58633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4670831/10000000) (δ := 7247/1000000000) (ψ := -100181/125000) 142 119
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t195 : ((-8399026389/400000000000 : ℚ) : ℝ) ≤ stT142 195 := by
  have hc : ((-58643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8399026389/400000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-58643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c196 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-854133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1621673/2500000) (δ := 1789/250000000) (ψ := -100181/125000) 142 119
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t196 : ((-305065479169/5000000000000 : ℚ) : ℝ) ≤ stT142 196 := by
  have hc : ((-854183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305065479169/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-854183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c197 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-492299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7414641/10000000) (δ := 357/50000000) (ψ := -100181/125000) 142 120
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t197 : ((-87691643151/1250000000000 : ℚ) : ℝ) ≤ stT142 197 := by
  have hc : ((-123081/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87691643151/1250000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-123081/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c198 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-625733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5617169/10000000) (δ := 7263/1000000000) (ψ := -100181/125000) 142 120
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t198 : ((-44472520461/1000000000000 : ℚ) : ℝ) ≤ stT142 198 := by
  have hc : ((-625783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44472520461/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-625783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c199 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((19643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3063/8000) (δ := 7263/1000000000) (ψ := -100181/125000) 142 120
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t199 : ((6953413729/2500000000000 : ℚ) : ℝ) ≤ stT142 199 := by
  have hc : ((9809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6953413729/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((9809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c200 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((341211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2049313/10000000) (δ := 357/50000000) (ψ := -100181/125000) 142 120
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t200 : ((60313666929/1250000000000 : ℚ) : ℝ) ≤ stT142 200 := by
  have hc : ((170593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60313666929/1250000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((170593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c201 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((15528/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55743/2000000) (δ := 357/50000000) (ψ := -100181/125000) 142 120
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t201 : ((70093095099/1000000000000 : ℚ) : ℝ) ≤ stT142 201 := by
  have hc : ((496871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70093095099/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((496871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c202 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((414573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370761/2500000) (δ := 7263/1000000000) (ψ := -100181/125000) 142 120
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t202 : ((72918682289/1250000000000 : ℚ) : ℝ) ≤ stT142 202 := by
  have hc : ((103637/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72918682289/1250000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((103637/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c203 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((272837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 161807/500000) (δ := 357/50000000) (ψ := -100181/125000) 142 120
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t203 : ((95729414697/5000000000000 : ℚ) : ℝ) ≤ stT142 203 := by
  have hc : ((272787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95729414697/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((272787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c204 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-204541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 498061/1000000) (δ := 357/50000000) (ψ := -100181/125000) 142 120
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t204 : ((-71612521903/2500000000000 : ℚ) : ℝ) ≤ stT142 204 := by
  have hc : ((-102283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71612521903/2500000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-102283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c205 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-35931/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83957/125000) (δ := 357/50000000) (ψ := -100181/125000) 142 120
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t205 : ((-25096721123/400000000000 : ℚ) : ℝ) ≤ stT142 205 := by
  have hc : ((-35933/40000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25096721123/400000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-35933/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c206 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-486137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3631951/5000000) (δ := 717/100000000) (ψ := -100181/125000) 142 121
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t206 : ((-84681398727/1250000000000 : ℚ) : ℝ) ≤ stT142 206 := by
  have hc : ((-243081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84681398727/1250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-243081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c207 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-602887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5544779/10000000) (δ := 717/100000000) (ψ := -100181/125000) 142 121
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t207 : ((-419070758913/10000000000000 : ℚ) : ℝ) ≤ stT142 207 := by
  have hc : ((-602937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419070758913/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-602937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c208 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((37217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479241/1250000) (δ := 7233/1000000000) (ψ := -100181/125000) 142 121
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t208 : ((206165349/80000000000 : ℚ) : ℝ) ≤ stT142 208 := by
  have hc : ((37167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206165349/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((37167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c209 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((131619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2131277/10000000) (δ := 7233/1000000000) (ψ := -100181/125000) 142 121
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t209 : ((45517893913/1000000000000 : ℚ) : ℝ) ≤ stT142 209 := by
  have hc : ((131609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45517893913/1000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((131609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c210 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((492389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87351/2000000) (δ := 717/100000000) (ψ := -100181/125000) 142 121
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t210 : ((16988158183/250000000000 : ℚ) : ℝ) ≤ stT142 210 := by
  have hc : ((123091/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16988158183/250000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((123091/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c211 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((877639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312427/2500000) (δ := 717/100000000) (ψ := -100181/125000) 142 121
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t211 : ((151039210023/2500000000000 : ℚ) : ℝ) ≤ stT142 211 := by
  have hc : ((877589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151039210023/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((877589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c212 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((388979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2928183/10000000) (δ := 7233/1000000000) (ψ := -100181/125000) 142 121
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t212 : ((133558607529/5000000000000 : ℚ) : ℝ) ≤ stT142 212 := by
  have hc : ((388929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133558607529/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((388929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c213 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-265493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2299389/5000000) (δ := 717/100000000) (ψ := -100181/125000) 142 121
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t213 : ((-181947142627/10000000000000 : ℚ) : ℝ) ≤ stT142 213 := by
  have hc : ((-265543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181947142627/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-265543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c214 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-803903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3130781/5000000) (δ := 7233/1000000000) (ψ := -100181/125000) 142 121
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t214 : ((-274785507729/5000000000000 : ℚ) : ℝ) ≤ stT142 214 := by
  have hc : ((-803953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274785507729/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-803953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c215 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-999687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7791391/10000000) (δ := 3563/500000000) (ψ := -100181/125000) 142 122
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t215 : ((-136363127063/2000000000000 : ℚ) : ℝ) ≤ stT142 215 := by
  have hc : ((-999737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136363127063/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-999737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c216 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-193767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6144049/10000000) (δ := 3563/500000000) (ψ := -100181/125000) 142 122
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t216 : ((-131850284713/2500000000000 : ℚ) : ℝ) ≤ stT142 216 := by
  have hc : ((-387559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131850284713/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-387559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c217 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-57223/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4504339/10000000) (δ := 7277/1000000000) (ψ := -100181/125000) 142 122
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t217 : ((-15541613199/1000000000000 : ℚ) : ℝ) ≤ stT142 217 := by
  have hc : ((-114471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15541613199/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-114471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c218 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((204763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -718039/2500000) (δ := 3563/500000000) (ψ := -100181/125000) 142 122
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t218 : ((13866597633/500000000000 : ℚ) : ℝ) ≤ stT142 218 := by
  have hc : ((102369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13866597633/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((102369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c219 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((219519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1247427/10000000) (δ := 7277/1000000000) (ψ := -100181/125000) 142 122
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t219 : ((296657327581/5000000000000 : ℚ) : ℝ) ≤ stT142 219 := by
  have hc : ((439013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296657327581/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((439013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c220 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((39563/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184941/5000000) (δ := 7277/1000000000) (ψ := -100181/125000) 142 122
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t220 : ((26671986639/400000000000 : ℚ) : ℝ) ≤ stT142 220 := by
  have hc : ((39561/40000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26671986639/400000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((39561/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c221 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((351229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 989939/5000000) (δ := 7277/1000000000) (ψ := -100181/125000) 142 122
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t221 : ((1845664821/39062500000 : ℚ) : ℝ) ≤ stT142 221 := by
  have hc : ((87801/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1845664821/39062500000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((87801/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c222 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((17167/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3582561/10000000) (δ := 7277/1000000000) (ψ := -100181/125000) 142 122
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t222 : ((11517540327/1250000000000 : ℚ) : ℝ) ≤ stT142 222 := by
  have hc : ((68643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11517540327/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((68643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c223 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-95961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5178073/10000000) (δ := 7277/1000000000) (ψ := -100181/125000) 142 122
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t223 : ((-1285339603/40000000000 : ℚ) : ℝ) ≤ stT142 223 := by
  have hc : ((-95971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1285339603/40000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-95971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c224 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-181373/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6766449/10000000) (δ := 3563/500000000) (ψ := -100181/125000) 142 122
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t224 : ((-60595888491/1000000000000 : ℚ) : ℝ) ≤ stT142 224 := by
  have hc : ((-181383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60595888491/1000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-181383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c225 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-490279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3680101/5000000) (δ := 1437/200000000) (ψ := -100181/125000) 142 123
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t225 : ((-5107335887/78125000000 : ℚ) : ℝ) ≤ stT142 225 := by
  have hc : ((-15322/15625 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5107335887/78125000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-15322/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c226 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-338463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5785937/10000000) (δ := 7109/500000000) (ψ := -100181/125000) 142 123
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t226 : ((-28144896401/625000000000 : ℚ) : ℝ) ≤ stT142 226 := by
  have hc : ((-42311/62500 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28144896401/625000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-42311/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c227 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-116377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2109297/5000000) (δ := 1437/200000000) (ψ := -100181/125000) 142 123
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t227 : ((-19318848537/2500000000000 : ℚ) : ℝ) ≤ stT142 227 := by
  have hc : ((-116427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19318848537/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-116427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c228 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((60753/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -664539/2500000) (δ := 1437/200000000) (ψ := -100181/125000) 142 123
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t228 : ((80461014271/2500000000000 : ℚ) : ℝ) ≤ stT142 228 := by
  have hc : ((242987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80461014271/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((242987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c229 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((451989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -552267/5000000) (δ := 1437/200000000) (ψ := -100181/125000) 142 123
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t229 : ((37333243319/625000000000 : ℚ) : ℝ) ≤ stT142 229 := by
  have hc : ((112991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37333243319/625000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((112991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c230 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((98439/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 442307/10000000) (δ := 3609/500000000) (ψ := -100181/125000) 142 123
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t230 : ((1622635273/25000000000 : ℚ) : ℝ) ≤ stT142 230 := by
  have hc : ((49217/50000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1622635273/25000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((49217/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c231 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((21929/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1982439/10000000) (δ := 3609/500000000) (ψ := -100181/125000) 142 123
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t231 : ((230834870889/5000000000000 : ℚ) : ℝ) ≤ stT142 231 := by
  have hc : ((350839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230834870889/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((350839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c232 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((163697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3515897/10000000) (δ := 3609/500000000) (ψ := -100181/125000) 142 123
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t232 : ((26859873051/2500000000000 : ℚ) : ℝ) ≤ stT142 232 := by
  have hc : ((163647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26859873051/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((163647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c233 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-13489/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1260697/2500000) (δ := 1437/200000000) (ψ := -100181/125000) 142 123
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t233 : ((-70703714289/2500000000000 : ℚ) : ℝ) ≤ stT142 233 := by
  have hc : ((-215849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70703714289/2500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-215849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c234 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-173927/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3281573/5000000) (δ := 3609/500000000) (ψ := -100181/125000) 142 123
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t234 : ((-113706269577/2000000000000 : ℚ) : ℝ) ≤ stT142 234 := by
  have hc : ((-173937/200000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113706269577/2000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-173937/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c235 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-996023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1526191/2000000) (δ := 7111/1000000000) (ψ := -100181/125000) 142 124
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t235 : ((-649767304017/10000000000000 : ℚ) : ℝ) ≤ stT142 235 := by
  have hc : ((-996073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-649767304017/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-996073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c236 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-769853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3061759/5000000) (δ := 1823/250000000) (ψ := -100181/125000) 142 124
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t236 : ((-100232901667/2000000000000 : ℚ) : ℝ) ≤ stT142 236 := by
  have hc : ((-769903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100232901667/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-769903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c237 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-137309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -577809/1250000) (δ := 7111/1000000000) (ψ := -100181/125000) 142 124
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t237 : ((-4460402319/250000000000 : ℚ) : ℝ) ≤ stT142 237 := by
  have hc : ((-68667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4460402319/250000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-68667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c238 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((314281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48871/156250) (δ := 1823/250000000) (ψ := -100181/125000) 142 124
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t238 : ((203685476893/10000000000000 : ℚ) : ℝ) ≤ stT142 238 := by
  have hc : ((314231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203685476893/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((314231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c239 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((396309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -327853/2000000) (δ := 7111/1000000000) (ψ := -100181/125000) 142 124
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t239 : ((32041840033/625000000000 : ℚ) : ℝ) ≤ stT142 239 := by
  have hc : ((99071/125000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32041840033/625000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((99071/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c240 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((998029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78499/5000000) (δ := 7111/1000000000) (ψ := -100181/125000) 142 124
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t240 : ((644192450563/10000000000000 : ℚ) : ℝ) ≤ stT142 240 := by
  have hc : ((997979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((644192450563/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((997979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c241 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((863999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329773/2500000) (δ := 7111/1000000000) (ψ := -100181/125000) 142 124
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t241 : ((139129483011/2500000000000 : ℚ) : ℝ) ≤ stT142 241 := by
  have hc : ((863949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139129483011/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((863949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c242 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((439611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697269/2500000) (δ := 7111/1000000000) (ψ := -100181/125000) 142 124
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t242 : ((35320045033/1250000000000 : ℚ) : ℝ) ≤ stT142 242 := by
  have hc : ((439561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35320045033/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((439561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c243 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-13003/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 425299/1000000) (δ := 1823/250000000) (ψ := -100181/125000) 142 124
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t243 : ((-521540313/62500000000 : ℚ) : ℝ) ≤ stT142 243 := by
  have hc : ((-813/6250 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521540313/62500000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-813/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c244 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-654533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 713863/1250000) (δ := 1823/250000000) (ψ := -100181/125000) 142 124
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t244 : ((-83810843571/2000000000000 : ℚ) : ℝ) ≤ stT142 244 := by
  have hc : ((-654583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83810843571/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-654583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c245 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-240507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1790709/2500000) (δ := 3573/250000000) (ψ := -100181/125000) 142 124
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t245 : ((-307324753203/5000000000000 : ℚ) : ℝ) ≤ stT142 245 := by
  have hc : ((-481039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307324753203/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-481039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c246 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-238689/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -443693/625000) (δ := 7199/1000000000) (ψ := -100181/125000) 142 125
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t246 : ((-304381172531/5000000000000 : ℚ) : ℝ) ≤ stT142 246 := by
  have hc : ((-477403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304381172531/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-477403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c247 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-319337/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414731/2500000) (δ := 7199/1000000000) (ψ := -100181/125000) 142 125
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t247 : ((-20320525017/500000000000 : ℚ) : ℝ) ≤ stT142 247 := by
  have hc : ((-159681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20320525017/500000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-159681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c248 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-29689/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2112291/5000000) (δ := 7199/1000000000) (ψ := -100181/125000) 142 125
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t248 : ((-37720964403/5000000000000 : ℚ) : ℝ) ≤ stT142 248 := by
  have hc : ((-59403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37720964403/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-59403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c249 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((54639/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2796027/10000000) (δ := 1801/250000000) (ψ := -100181/125000) 142 125
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t249 : ((34622084861/1250000000000 : ℚ) : ℝ) ≤ stT142 249 := by
  have hc : ((218531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34622084861/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((218531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_c250 :
    |Real.cos (((142 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((852911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1373151/10000000) (δ := 7199/1000000000) (ψ := -100181/125000) 142 125
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st142_t250 : ((107879240751/2000000000000 : ℚ) : ℝ) ≤ stT142 250 := by
  have hc : ((852861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((142 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st142_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107879240751/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((852861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st142_p1 : ((695617/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT142 (i+1) := by
  rw [Finset.sum_range_one]
  exact st142_t1

theorem st142_p2 : ((4414725605887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT142 (i+1))
      = (∑ i ∈ Finset.range 1, stT142 (i+1)) + stT142 2 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 1
    simpa using h
  have hprev := st142_p1
  have hstep := st142_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p3 : ((3596336036973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT142 (i+1))
      = (∑ i ∈ Finset.range 2, stT142 (i+1)) + stT142 3 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 2
    simpa using h
  have hprev := st142_p2
  have hstep := st142_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p4 : ((9559748182773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT142 (i+1))
      = (∑ i ∈ Finset.range 3, stT142 (i+1)) + stT142 4 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 3
    simpa using h
  have hprev := st142_p3
  have hstep := st142_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p5 : ((5087451185877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT142 (i+1))
      = (∑ i ∈ Finset.range 4, stT142 (i+1)) + stT142 5 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 4
    simpa using h
  have hprev := st142_p4
  have hstep := st142_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p6 : ((2134550407147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT142 (i+1))
      = (∑ i ∈ Finset.range 5, stT142 (i+1)) + stT142 6 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 5
    simpa using h
  have hprev := st142_p5
  have hstep := st142_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p7 : ((5119010224563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT142 (i+1))
      = (∑ i ∈ Finset.range 6, stT142 (i+1)) + stT142 7 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 6
    simpa using h
  have hprev := st142_p6
  have hstep := st142_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p8 : ((239094408543/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT142 (i+1))
      = (∑ i ∈ Finset.range 7, stT142 (i+1)) + stT142 8 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 7
    simpa using h
  have hprev := st142_p7
  have hstep := st142_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p9 : ((523412145897/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT142 (i+1))
      = (∑ i ∈ Finset.range 8, stT142 (i+1)) + stT142 9 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 8
    simpa using h
  have hprev := st142_p8
  have hstep := st142_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p10 : ((2491839341151/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT142 (i+1))
      = (∑ i ∈ Finset.range 9, stT142 (i+1)) + stT142 10 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 9
    simpa using h
  have hprev := st142_p9
  have hstep := st142_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p11 : ((271361752983/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT142 (i+1))
      = (∑ i ∈ Finset.range 10, stT142 (i+1)) + stT142 11 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 10
    simpa using h
  have hprev := st142_p10
  have hstep := st142_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p12 : ((250877360791/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT142 (i+1))
      = (∑ i ∈ Finset.range 11, stT142 (i+1)) + stT142 12 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 11
    simpa using h
  have hprev := st142_p11
  have hstep := st142_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p13 : ((2579443631453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT142 (i+1))
      = (∑ i ∈ Finset.range 12, stT142 (i+1)) + stT142 13 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 12
    simpa using h
  have hprev := st142_p12
  have hstep := st142_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p14 : ((2664216211481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT142 (i+1))
      = (∑ i ∈ Finset.range 13, stT142 (i+1)) + stT142 14 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 13
    simpa using h
  have hprev := st142_p13
  have hstep := st142_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p15 : ((4710017655583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT142 (i+1))
      = (∑ i ∈ Finset.range 14, stT142 (i+1)) + stT142 15 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 14
    simpa using h
  have hprev := st142_p14
  have hstep := st142_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p16 : ((5006078905583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT142 (i+1))
      = (∑ i ∈ Finset.range 15, stT142 (i+1)) + stT142 16 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 15
    simpa using h
  have hprev := st142_p15
  have hstep := st142_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p17 : ((226698405893/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT142 (i+1))
      = (∑ i ∈ Finset.range 16, stT142 (i+1)) + stT142 17 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 16
    simpa using h
  have hprev := st142_p16
  have hstep := st142_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p18 : ((4546657998457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT142 (i+1))
      = (∑ i ∈ Finset.range 17, stT142 (i+1)) + stT142 18 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 17
    simpa using h
  have hprev := st142_p17
  have hstep := st142_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p19 : ((2002952728757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT142 (i+1))
      = (∑ i ∈ Finset.range 18, stT142 (i+1)) + stT142 19 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 18
    simpa using h
  have hprev := st142_p18
  have hstep := st142_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p20 : ((4551279962747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT142 (i+1))
      = (∑ i ∈ Finset.range 19, stT142 (i+1)) + stT142 20 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 19
    simpa using h
  have hprev := st142_p19
  have hstep := st142_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p21 : ((221967685773/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT142 (i+1))
      = (∑ i ∈ Finset.range 20, stT142 (i+1)) + stT142 21 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 20
    simpa using h
  have hprev := st142_p20
  have hstep := st142_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p22 : ((3305243020431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT142 (i+1))
      = (∑ i ∈ Finset.range 21, stT142 (i+1)) + stT142 22 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 21
    simpa using h
  have hprev := st142_p21
  have hstep := st142_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p23 : ((765083631993/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT142 (i+1))
      = (∑ i ∈ Finset.range 22, stT142 (i+1)) + stT142 23 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 22
    simpa using h
  have hprev := st142_p22
  have hstep := st142_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p24 : ((17249063502403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT142 (i+1))
      = (∑ i ∈ Finset.range 23, stT142 (i+1)) + stT142 24 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 23
    simpa using h
  have hprev := st142_p23
  have hstep := st142_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p25 : ((18655647502403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT142 (i+1))
      = (∑ i ∈ Finset.range 24, stT142 (i+1)) + stT142 25 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 24
    simpa using h
  have hprev := st142_p24
  have hstep := st142_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p26 : ((9392682287213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT142 (i+1))
      = (∑ i ∈ Finset.range 25, stT142 (i+1)) + stT142 26 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 25
    simpa using h
  have hprev := st142_p25
  have hstep := st142_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p27 : ((17329539227457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT142 (i+1))
      = (∑ i ∈ Finset.range 26, stT142 (i+1)) + stT142 27 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 26
    simpa using h
  have hprev := st142_p26
  have hstep := st142_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p28 : ((77966236689/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT142 (i+1))
      = (∑ i ∈ Finset.range 27, stT142 (i+1)) + stT142 28 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 27
    simpa using h
  have hprev := st142_p27
  have hstep := st142_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p29 : ((7921929000387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT142 (i+1))
      = (∑ i ∈ Finset.range 28, stT142 (i+1)) + stT142 29 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 28
    simpa using h
  have hprev := st142_p28
  have hstep := st142_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p30 : ((17668465215613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT142 (i+1))
      = (∑ i ∈ Finset.range 29, stT142 (i+1)) + stT142 30 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 29
    simpa using h
  have hprev := st142_p29
  have hstep := st142_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p31 : ((17506911954367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT142 (i+1))
      = (∑ i ∈ Finset.range 30, stT142 (i+1)) + stT142 31 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 30
    simpa using h
  have hprev := st142_p30
  have hstep := st142_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p32 : ((7907477821081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT142 (i+1))
      = (∑ i ∈ Finset.range 31, stT142 (i+1)) + stT142 32 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 31
    simpa using h
  have hprev := st142_p31
  have hstep := st142_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p33 : ((8425070582653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT142 (i+1))
      = (∑ i ∈ Finset.range 32, stT142 (i+1)) + stT142 33 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 32
    simpa using h
  have hprev := st142_p32
  have hstep := st142_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p34 : ((8806184839263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT142 (i+1))
      = (∑ i ∈ Finset.range 33, stT142 (i+1)) + stT142 34 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 33
    simpa using h
  have hprev := st142_p33
  have hstep := st142_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p35 : ((1992184959653/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT142 (i+1))
      = (∑ i ∈ Finset.range 34, stT142 (i+1)) + stT142 35 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 34
    simpa using h
  have hprev := st142_p34
  have hstep := st142_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p36 : ((8593480422049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT142 (i+1))
      = (∑ i ∈ Finset.range 35, stT142 (i+1)) + stT142 36 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 35
    simpa using h
  have hprev := st142_p35
  have hstep := st142_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p37 : ((8512520490509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT142 (i+1))
      = (∑ i ∈ Finset.range 36, stT142 (i+1)) + stT142 37 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 36
    simpa using h
  have hprev := st142_p36
  have hstep := st142_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p38 : ((8090815967969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT142 (i+1))
      = (∑ i ∈ Finset.range 37, stT142 (i+1)) + stT142 38 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 37
    simpa using h
  have hprev := st142_p37
  have hstep := st142_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p39 : ((17603961777783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT142 (i+1))
      = (∑ i ∈ Finset.range 38, stT142 (i+1)) + stT142 39 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 38
    simpa using h
  have hprev := st142_p38
  have hstep := st142_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p40 : ((8011592429307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT142 (i+1))
      = (∑ i ∈ Finset.range 39, stT142 (i+1)) + stT142 40 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 39
    simpa using h
  have hprev := st142_p39
  have hstep := st142_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p41 : ((3498972234207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT142 (i+1))
      = (∑ i ∈ Finset.range 40, stT142 (i+1)) + stT142 41 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 40
    simpa using h
  have hprev := st142_p40
  have hstep := st142_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p42 : ((16240180106751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT142 (i+1))
      = (∑ i ∈ Finset.range 41, stT142 (i+1)) + stT142 42 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 41
    simpa using h
  have hprev := st142_p41
  have hstep := st142_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p43 : ((269988018929/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT142 (i+1))
      = (∑ i ∈ Finset.range 42, stT142 (i+1)) + stT142 43 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 42
    simpa using h
  have hprev := st142_p42
  have hstep := st142_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p44 : ((16394937964181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT142 (i+1))
      = (∑ i ∈ Finset.range 43, stT142 (i+1)) + stT142 44 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 43
    simpa using h
  have hprev := st142_p43
  have hstep := st142_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p45 : ((3441667095413/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT142 (i+1))
      = (∑ i ∈ Finset.range 44, stT142 (i+1)) + stT142 45 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 44
    simpa using h
  have hprev := st142_p44
  have hstep := st142_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p46 : ((3275682789493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT142 (i+1))
      = (∑ i ∈ Finset.range 45, stT142 (i+1)) + stT142 46 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 45
    simpa using h
  have hprev := st142_p45
  have hstep := st142_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p47 : ((8650878863451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT142 (i+1))
      = (∑ i ∈ Finset.range 46, stT142 (i+1)) + stT142 47 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 46
    simpa using h
  have hprev := st142_p46
  have hstep := st142_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p48 : ((8114642307123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT142 (i+1))
      = (∑ i ∈ Finset.range 47, stT142 (i+1)) + stT142 48 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 47
    simpa using h
  have hprev := st142_p47
  have hstep := st142_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p49 : ((8734613549703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT142 (i+1))
      = (∑ i ∈ Finset.range 48, stT142 (i+1)) + stT142 49 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 48
    simpa using h
  have hprev := st142_p48
  have hstep := st142_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p50 : ((1609780155819/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT142 (i+1))
      = (∑ i ∈ Finset.range 49, stT142 (i+1)) + stT142 50 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 49
    simpa using h
  have hprev := st142_p49
  have hstep := st142_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p51 : ((1749321418491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT142 (i+1))
      = (∑ i ∈ Finset.range 50, stT142 (i+1)) + stT142 51 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 50
    simpa using h
  have hprev := st142_p50
  have hstep := st142_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p52 : ((1015931139903/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT142 (i+1))
      = (∑ i ∈ Finset.range 51, stT142 (i+1)) + stT142 52 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 51
    simpa using h
  have hprev := st142_p51
  have hstep := st142_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p53 : ((2138076286431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT142 (i+1))
      = (∑ i ∈ Finset.range 52, stT142 (i+1)) + stT142 53 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 52
    simpa using h
  have hprev := st142_p52
  have hstep := st142_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p54 : ((526915700313/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT142 (i+1))
      = (∑ i ∈ Finset.range 53, stT142 (i+1)) + stT142 54 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 53
    simpa using h
  have hprev := st142_p53
  have hstep := st142_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p55 : ((16006724709/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT142 (i+1))
      = (∑ i ∈ Finset.range 54, stT142 (i+1)) + stT142 55 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 54
    simpa using h
  have hprev := st142_p54
  have hstep := st142_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p56 : ((4367348655277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT142 (i+1))
      = (∑ i ∈ Finset.range 55, stT142 (i+1)) + stT142 56 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 55
    simpa using h
  have hprev := st142_p55
  have hstep := st142_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p57 : ((16144802017123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT142 (i+1))
      = (∑ i ∈ Finset.range 56, stT142 (i+1)) + stT142 57 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 56
    simpa using h
  have hprev := st142_p56
  have hstep := st142_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p58 : ((17175013648627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT142 (i+1))
      = (∑ i ∈ Finset.range 57, stT142 (i+1)) + stT142 58 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 57
    simpa using h
  have hprev := st142_p57
  have hstep := st142_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p59 : ((16931733369997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT142 (i+1))
      = (∑ i ∈ Finset.range 58, stT142 (i+1)) + stT142 59 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 58
    simpa using h
  have hprev := st142_p58
  have hstep := st142_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p60 : ((2029775227379/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT142 (i+1))
      = (∑ i ∈ Finset.range 59, stT142 (i+1)) + stT142 60 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 59
    simpa using h
  have hprev := st142_p59
  have hstep := st142_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p61 : ((87452815247/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT142 (i+1))
      = (∑ i ∈ Finset.range 60, stT142 (i+1)) + stT142 61 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 60
    simpa using h
  have hprev := st142_p60
  have hstep := st142_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p62 : ((4114828451347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT142 (i+1))
      = (∑ i ∈ Finset.range 61, stT142 (i+1)) + stT142 62 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 61
    simpa using h
  have hprev := st142_p61
  have hstep := st142_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p63 : ((16557371603499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT142 (i+1))
      = (∑ i ∈ Finset.range 62, stT142 (i+1)) + stT142 63 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 62
    simpa using h
  have hprev := st142_p62
  have hstep := st142_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p64 : ((17477505353499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT142 (i+1))
      = (∑ i ∈ Finset.range 63, stT142 (i+1)) + stT142 64 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 63
    simpa using h
  have hprev := st142_p63
  have hstep := st142_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p65 : ((16260983198231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT142 (i+1))
      = (∑ i ∈ Finset.range 64, stT142 (i+1)) + stT142 65 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 64
    simpa using h
  have hprev := st142_p64
  have hstep := st142_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p66 : ((16740958417907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT142 (i+1))
      = (∑ i ∈ Finset.range 65, stT142 (i+1)) + stT142 66 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 65
    simpa using h
  have hprev := st142_p65
  have hstep := st142_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p67 : ((3487269817219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT142 (i+1))
      = (∑ i ∈ Finset.range 66, stT142 (i+1)) + stT142 67 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 66
    simpa using h
  have hprev := st142_p66
  have hstep := st142_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p68 : ((16226808499347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT142 (i+1))
      = (∑ i ∈ Finset.range 67, stT142 (i+1)) + stT142 68 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 67
    simpa using h
  have hprev := st142_p67
  have hstep := st142_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p69 : ((16728147940299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT142 (i+1))
      = (∑ i ∈ Finset.range 68, stT142 (i+1)) + stT142 69 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 68
    simpa using h
  have hprev := st142_p68
  have hstep := st142_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p70 : ((17469195276439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT142 (i+1))
      = (∑ i ∈ Finset.range 69, stT142 (i+1)) + stT142 70 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 69
    simpa using h
  have hprev := st142_p69
  have hstep := st142_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p71 : ((16312372401247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT142 (i+1))
      = (∑ i ∈ Finset.range 70, stT142 (i+1)) + stT142 71 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 70
    simpa using h
  have hprev := st142_p70
  have hstep := st142_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p72 : ((16534726785661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT142 (i+1))
      = (∑ i ∈ Finset.range 71, stT142 (i+1)) + stT142 72 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 71
    simpa using h
  have hprev := st142_p71
  have hstep := st142_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p73 : ((8757568387577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT142 (i+1))
      = (∑ i ∈ Finset.range 72, stT142 (i+1)) + stT142 73 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 72
    simpa using h
  have hprev := st142_p72
  have hstep := st142_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p74 : ((3315411239579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT142 (i+1))
      = (∑ i ∈ Finset.range 73, stT142 (i+1)) + stT142 74 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 73
    simpa using h
  have hprev := st142_p73
  have hstep := st142_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p75 : ((4059878789069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT142 (i+1))
      = (∑ i ∈ Finset.range 74, stT142 (i+1)) + stT142 75 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 74
    simpa using h
  have hprev := st142_p74
  have hstep := st142_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p76 : ((4346608141339/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT142 (i+1))
      = (∑ i ∈ Finset.range 75, stT142 (i+1)) + stT142 76 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 75
    simpa using h
  have hprev := st142_p75
  have hstep := st142_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p77 : ((426270863821/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT142 (i+1))
      = (∑ i ∈ Finset.range 76, stT142 (i+1)) + stT142 77 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 76
    simpa using h
  have hprev := st142_p76
  have hstep := st142_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p78 : ((4022915369509/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT142 (i+1))
      = (∑ i ∈ Finset.range 77, stT142 (i+1)) + stT142 78 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 77
    simpa using h
  have hprev := st142_p77
  have hstep := st142_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p79 : ((4224377948077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT142 (i+1))
      = (∑ i ∈ Finset.range 78, stT142 (i+1)) + stT142 79 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 78
    simpa using h
  have hprev := st142_p78
  have hstep := st142_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p80 : ((17488409003303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT142 (i+1))
      = (∑ i ∈ Finset.range 79, stT142 (i+1)) + stT142 80 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 79
    simpa using h
  have hprev := st142_p79
  have hstep := st142_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p81 : ((16449927061407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT142 (i+1))
      = (∑ i ∈ Finset.range 80, stT142 (i+1)) + stT142 81 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 80
    simpa using h
  have hprev := st142_p80
  have hstep := st142_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p82 : ((16238977306139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT142 (i+1))
      = (∑ i ∈ Finset.range 81, stT142 (i+1)) + stT142 82 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 81
    simpa using h
  have hprev := st142_p81
  have hstep := st142_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p83 : ((17335609475499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT142 (i+1))
      = (∑ i ∈ Finset.range 82, stT142 (i+1)) + stT142 83 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 82
    simpa using h
  have hprev := st142_p82
  have hstep := st142_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p84 : ((17239546638629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT142 (i+1))
      = (∑ i ∈ Finset.range 83, stT142 (i+1)) + stT142 84 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 83
    simpa using h
  have hprev := st142_p83
  have hstep := st142_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p85 : ((8087994527413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT142 (i+1))
      = (∑ i ∈ Finset.range 84, stT142 (i+1)) + stT142 85 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 84
    simpa using h
  have hprev := st142_p84
  have hstep := st142_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p86 : ((4120512651809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT142 (i+1))
      = (∑ i ∈ Finset.range 85, stT142 (i+1)) + stT142 86 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 85
    simpa using h
  have hprev := st142_p85
  have hstep := st142_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p87 : ((4371469412433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT142 (i+1))
      = (∑ i ∈ Finset.range 86, stT142 (i+1)) + stT142 87 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 86
    simpa using h
  have hprev := st142_p86
  have hstep := st142_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p88 : ((4265038507069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT142 (i+1))
      = (∑ i ∈ Finset.range 87, stT142 (i+1)) + stT142 88 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 87
    simpa using h
  have hprev := st142_p87
  have hstep := st142_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p89 : ((8051554167013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT142 (i+1))
      = (∑ i ∈ Finset.range 88, stT142 (i+1)) + stT142 89 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 88
    simpa using h
  have hprev := st142_p88
  have hstep := st142_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p90 : ((8285656932247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT142 (i+1))
      = (∑ i ∈ Finset.range 89, stT142 (i+1)) + stT142 90 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 89
    simpa using h
  have hprev := st142_p89
  have hstep := st142_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p91 : ((8755615752997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT142 (i+1))
      = (∑ i ∈ Finset.range 90, stT142 (i+1)) + stT142 91 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 90
    simpa using h
  have hprev := st142_p90
  have hstep := st142_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p92 : ((8533683238487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT142 (i+1))
      = (∑ i ∈ Finset.range 91, stT142 (i+1)) + stT142 92 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 91
    simpa using h
  have hprev := st142_p91
  have hstep := st142_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p93 : ((8056936260871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT142 (i+1))
      = (∑ i ∈ Finset.range 92, stT142 (i+1)) + stT142 93 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 92
    simpa using h
  have hprev := st142_p92
  have hstep := st142_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p94 : ((16469441503019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT142 (i+1))
      = (∑ i ∈ Finset.range 93, stT142 (i+1)) + stT142 94 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 93
    simpa using h
  have hprev := st142_p93
  have hstep := st142_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p95 : ((17454306512603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT142 (i+1))
      = (∑ i ∈ Finset.range 94, stT142 (i+1)) + stT142 95 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 94
    simpa using h
  have hprev := st142_p94
  have hstep := st142_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p96 : ((17251486666241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT142 (i+1))
      = (∑ i ∈ Finset.range 95, stT142 (i+1)) + stT142 96 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 95
    simpa using h
  have hprev := st142_p95
  have hstep := st142_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p97 : ((16241234677487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT142 (i+1))
      = (∑ i ∈ Finset.range 96, stT142 (i+1)) + stT142 97 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 96
    simpa using h
  have hprev := st142_p96
  have hstep := st142_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p98 : ((811369829577/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT142 (i+1))
      = (∑ i ∈ Finset.range 97, stT142 (i+1)) + stT142 98 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 97
    simpa using h
  have hprev := st142_p97
  have hstep := st142_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p99 : ((17222153068067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT142 (i+1))
      = (∑ i ∈ Finset.range 98, stT142 (i+1)) + stT142 99 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 98
    simpa using h
  have hprev := st142_p98
  have hstep := st142_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p100 : ((437616494639/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT142 (i+1))
      = (∑ i ∈ Finset.range 99, stT142 (i+1)) + stT142 100 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 99
    simpa using h
  have hprev := st142_p99
  have hstep := st142_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p101 : ((4151544570751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT142 (i+1))
      = (∑ i ∈ Finset.range 100, stT142 (i+1)) + stT142 101 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 100
    simpa using h
  have hprev := st142_p100
  have hstep := st142_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p102 : ((2004248820827/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT142 (i+1))
      = (∑ i ∈ Finset.range 101, stT142 (i+1)) + stT142 102 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 101
    simpa using h
  have hprev := st142_p101
  have hstep := st142_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p103 : ((3343873339553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT142 (i+1))
      = (∑ i ∈ Finset.range 102, stT142 (i+1)) + stT142 103 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 102
    simpa using h
  have hprev := st142_p102
  have hstep := st142_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p104 : ((3508921819529/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT142 (i+1))
      = (∑ i ∈ Finset.range 103, stT142 (i+1)) + stT142 104 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 103
    simpa using h
  have hprev := st142_p103
  have hstep := st142_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p105 : ((3440417472933/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT142 (i+1))
      = (∑ i ∈ Finset.range 104, stT142 (i+1)) + stT142 105 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 104
    simpa using h
  have hprev := st142_p104
  have hstep := st142_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p106 : ((3247885276869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT142 (i+1))
      = (∑ i ∈ Finset.range 105, stT142 (i+1)) + stT142 106 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 105
    simpa using h
  have hprev := st142_p105
  have hstep := st142_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p107 : ((16139305300203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT142 (i+1))
      = (∑ i ∈ Finset.range 106, stT142 (i+1)) + stT142 107 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 106
    simpa using h
  have hprev := st142_p106
  have hstep := st142_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p108 : ((17041989138453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT142 (i+1))
      = (∑ i ∈ Finset.range 107, stT142 (i+1)) + stT142 108 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 107
    simpa using h
  have hprev := st142_p107
  have hstep := st142_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p109 : ((17595033081723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT142 (i+1))
      = (∑ i ∈ Finset.range 108, stT142 (i+1)) + stT142 109 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 108
    simpa using h
  have hprev := st142_p108
  have hstep := st142_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p110 : ((16994551618953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT142 (i+1))
      = (∑ i ∈ Finset.range 109, stT142 (i+1)) + stT142 110 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 109
    simpa using h
  have hprev := st142_p109
  have hstep := st142_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p111 : ((3223724041899/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT142 (i+1))
      = (∑ i ∈ Finset.range 110, stT142 (i+1)) + stT142 111 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 110
    simpa using h
  have hprev := st142_p110
  have hstep := st142_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p112 : ((1621126400849/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT142 (i+1))
      = (∑ i ∈ Finset.range 111, stT142 (i+1)) + stT142 112 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 111
    simpa using h
  have hprev := st142_p111
  have hstep := st142_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p113 : ((1713121008873/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT142 (i+1))
      = (∑ i ∈ Finset.range 112, stT142 (i+1)) + stT142 113 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 112
    simpa using h
  have hprev := st142_p112
  have hstep := st142_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p114 : ((1760463507453/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT142 (i+1))
      = (∑ i ∈ Finset.range 113, stT142 (i+1)) + stT142 114 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 113
    simpa using h
  have hprev := st142_p113
  have hstep := st142_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p115 : ((3399323327379/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT142 (i+1))
      = (∑ i ∈ Finset.range 114, stT142 (i+1)) + stT142 115 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 114
    simpa using h
  have hprev := st142_p114
  have hstep := st142_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p116 : ((3226106658259/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT142 (i+1))
      = (∑ i ∈ Finset.range 115, stT142 (i+1)) + stT142 116 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 115
    simpa using h
  have hprev := st142_p115
  have hstep := st142_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p117 : ((3229227955159/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT142 (i+1))
      = (∑ i ∈ Finset.range 116, stT142 (i+1)) + stT142 117 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 116
    simpa using h
  have hprev := st142_p116
  have hstep := st142_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p118 : ((17012316137561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT142 (i+1))
      = (∑ i ∈ Finset.range 117, stT142 (i+1)) + stT142 118 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 117
    simpa using h
  have hprev := st142_p117
  have hstep := st142_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p119 : ((3523046232451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT142 (i+1))
      = (∑ i ∈ Finset.range 118, stT142 (i+1)) + stT142 119 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 118
    simpa using h
  have hprev := st142_p118
  have hstep := st142_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p120 : ((17201379268663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT142 (i+1))
      = (∑ i ∈ Finset.range 119, stT142 (i+1)) + stT142 120 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 119
    simpa using h
  have hprev := st142_p119
  have hstep := st142_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p121 : ((16295013723481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT142 (i+1))
      = (∑ i ∈ Finset.range 120, stT142 (i+1)) + stT142 121 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 120
    simpa using h
  have hprev := st142_p120
  have hstep := st142_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p122 : ((16006767654157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT142 (i+1))
      = (∑ i ∈ Finset.range 121, stT142 (i+1)) + stT142 122 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 121
    simpa using h
  have hprev := st142_p121
  have hstep := st142_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p123 : ((66701049383/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT142 (i+1))
      = (∑ i ∈ Finset.range 122, stT142 (i+1)) + stT142 123 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 122
    simpa using h
  have hprev := st142_p122
  have hstep := st142_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p124 : ((546790459111/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT142 (i+1))
      = (∑ i ∈ Finset.range 123, stT142 (i+1)) + stT142 124 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 123
    simpa using h
  have hprev := st142_p123
  have hstep := st142_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p125 : ((437788885891/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT142 (i+1))
      = (∑ i ∈ Finset.range 124, stT142 (i+1)) + stT142 125 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 124
    simpa using h
  have hprev := st142_p124
  have hstep := st142_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p126 : ((2088924560543/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT142 (i+1))
      = (∑ i ∈ Finset.range 125, stT142 (i+1)) + stT142 126 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 125
    simpa using h
  have hprev := st142_p125
  have hstep := st142_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p127 : ((4003573093643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT142 (i+1))
      = (∑ i ∈ Finset.range 126, stT142 (i+1)) + stT142 127 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 126
    simpa using h
  have hprev := st142_p126
  have hstep := st142_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p128 : ((8099318390409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT142 (i+1))
      = (∑ i ∈ Finset.range 127, stT142 (i+1)) + stT142 128 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 127
    simpa using h
  have hprev := st142_p127
  have hstep := st142_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p129 : ((8525222871159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT142 (i+1))
      = (∑ i ∈ Finset.range 128, stT142 (i+1)) + stT142 129 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 128
    simpa using h
  have hprev := st142_p128
  have hstep := st142_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p130 : ((2204397648497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT142 (i+1))
      = (∑ i ∈ Finset.range 129, stT142 (i+1)) + stT142 130 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 129
    simpa using h
  have hprev := st142_p129
  have hstep := st142_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p131 : ((17328751001851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT142 (i+1))
      = (∑ i ∈ Finset.range 130, stT142 (i+1)) + stT142 131 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 130
    simpa using h
  have hprev := st142_p130
  have hstep := st142_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p132 : ((8232982424883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT142 (i+1))
      = (∑ i ∈ Finset.range 131, stT142 (i+1)) + stT142 132 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 131
    simpa using h
  have hprev := st142_p131
  have hstep := st142_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p133 : ((7976923107663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT142 (i+1))
      = (∑ i ∈ Finset.range 132, stT142 (i+1)) + stT142 133 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 132
    simpa using h
  have hprev := st142_p132
  have hstep := st142_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p134 : ((8157718153977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT142 (i+1))
      = (∑ i ∈ Finset.range 133, stT142 (i+1)) + stT142 134 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 133
    simpa using h
  have hprev := st142_p133
  have hstep := st142_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p135 : ((4293271282573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT142 (i+1))
      = (∑ i ∈ Finset.range 134, stT142 (i+1)) + stT142 135 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 134
    simpa using h
  have hprev := st142_p134
  have hstep := st142_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p136 : ((4415351561121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT142 (i+1))
      = (∑ i ∈ Finset.range 135, stT142 (i+1)) + stT142 136 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 135
    simpa using h
  have hprev := st142_p135
  have hstep := st142_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p137 : ((4325452594929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT142 (i+1))
      = (∑ i ∈ Finset.range 136, stT142 (i+1)) + stT142 137 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 136
    simpa using h
  have hprev := st142_p136
  have hstep := st142_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p138 : ((1645508376947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT142 (i+1))
      = (∑ i ∈ Finset.range 137, stT142 (i+1)) + stT142 138 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 137
    simpa using h
  have hprev := st142_p137
  have hstep := st142_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p139 : ((15942262762747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT142 (i+1))
      = (∑ i ∈ Finset.range 138, stT142 (i+1)) + stT142 139 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 138
    simpa using h
  have hprev := st142_p138
  have hstep := st142_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p140 : ((16246830909727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT142 (i+1))
      = (∑ i ∈ Finset.range 139, stT142 (i+1)) + stT142 140 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 139
    simpa using h
  have hprev := st142_p139
  have hstep := st142_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p141 : ((133387184363/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT142 (i+1))
      = (∑ i ∈ Finset.range 140, stT142 (i+1)) + stT142 141 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 140
    simpa using h
  have hprev := st142_p140
  have hstep := st142_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p142 : ((3530166609509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT142 (i+1))
      = (∑ i ∈ Finset.range 141, stT142 (i+1)) + stT142 142 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 141
    simpa using h
  have hprev := st142_p141
  have hstep := st142_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p143 : ((17453770712109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT142 (i+1))
      = (∑ i ∈ Finset.range 142, stT142 (i+1)) + stT142 143 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 142
    simpa using h
  have hprev := st142_p142
  have hstep := st142_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p144 : ((16669054251003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT142 (i+1))
      = (∑ i ∈ Finset.range 143, stT142 (i+1)) + stT142 144 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 143
    simpa using h
  have hprev := st142_p143
  have hstep := st142_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p145 : ((16002557642563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT142 (i+1))
      = (∑ i ∈ Finset.range 144, stT142 (i+1)) + stT142 145 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 144
    simpa using h
  have hprev := st142_p144
  have hstep := st142_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p146 : ((16039290062883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT142 (i+1))
      = (∑ i ∈ Finset.range 145, stT142 (i+1)) + stT142 146 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 145
    simpa using h
  have hprev := st142_p145
  have hstep := st142_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p147 : ((16739333778671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT142 (i+1))
      = (∑ i ∈ Finset.range 146, stT142 (i+1)) + stT142 147 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 146
    simpa using h
  have hprev := st142_p146
  have hstep := st142_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p148 : ((17494579399889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT142 (i+1))
      = (∑ i ∈ Finset.range 147, stT142 (i+1)) + stT142 148 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 147
    simpa using h
  have hprev := st142_p147
  have hstep := st142_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p149 : ((17664438755429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT142 (i+1))
      = (∑ i ∈ Finset.range 148, stT142 (i+1)) + stT142 149 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 148
    simpa using h
  have hprev := st142_p148
  have hstep := st142_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p150 : ((8556645516487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT142 (i+1))
      = (∑ i ∈ Finset.range 149, stT142 (i+1)) + stT142 150 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 149
    simpa using h
  have hprev := st142_p149
  have hstep := st142_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p151 : ((2038088988769/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT142 (i+1))
      = (∑ i ∈ Finset.range 150, stT142 (i+1)) + stT142 151 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 150
    simpa using h
  have hprev := st142_p150
  have hstep := st142_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p152 : ((3975439783377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT142 (i+1))
      = (∑ i ∈ Finset.range 151, stT142 (i+1)) + stT142 152 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 151
    simpa using h
  have hprev := st142_p151
  have hstep := st142_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p153 : ((126757383567/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT142 (i+1))
      = (∑ i ∈ Finset.range 152, stT142 (i+1)) + stT142 153 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 152
    simpa using h
  have hprev := st142_p152
  have hstep := st142_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p154 : ((2126086349633/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT142 (i+1))
      = (∑ i ∈ Finset.range 153, stT142 (i+1)) + stT142 154 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 153
    simpa using h
  have hprev := st142_p153
  have hstep := st142_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p155 : ((8815416856071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT142 (i+1))
      = (∑ i ∈ Finset.range 154, stT142 (i+1)) + stT142 155 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 154
    simpa using h
  have hprev := st142_p154
  have hstep := st142_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p156 : ((1760911072053/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT142 (i+1))
      = (∑ i ∈ Finset.range 155, stT142 (i+1)) + stT142 156 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 155
    simpa using h
  have hprev := st142_p155
  have hstep := st142_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p157 : ((135737579001/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT142 (i+1))
      = (∑ i ∈ Finset.range 156, stT142 (i+1)) + stT142 157 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 156
    simpa using h
  have hprev := st142_p156
  have hstep := st142_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p158 : ((16199417873811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT142 (i+1))
      = (∑ i ∈ Finset.range 157, stT142 (i+1)) + stT142 158 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 157
    simpa using h
  have hprev := st142_p157
  have hstep := st142_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p159 : ((15883505609611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT142 (i+1))
      = (∑ i ∈ Finset.range 158, stT142 (i+1)) + stT142 159 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 158
    simpa using h
  have hprev := st142_p158
  have hstep := st142_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p160 : ((16248969846931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT142 (i+1))
      = (∑ i ∈ Finset.range 159, stT142 (i+1)) + stT142 160 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 159
    simpa using h
  have hprev := st142_p159
  have hstep := st142_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p161 : ((17020466488131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT142 (i+1))
      = (∑ i ∈ Finset.range 160, stT142 (i+1)) + stT142 161 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 160
    simpa using h
  have hprev := st142_p160
  have hstep := st142_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p162 : ((17634387437687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT142 (i+1))
      = (∑ i ∈ Finset.range 161, stT142 (i+1)) + stT142 162 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 161
    simpa using h
  have hprev := st142_p161
  have hstep := st142_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p163 : ((17652458029147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT142 (i+1))
      = (∑ i ∈ Finset.range 162, stT142 (i+1)) + stT142 163 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 162
    simpa using h
  have hprev := st142_p162
  have hstep := st142_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p164 : ((1066759775103/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT142 (i+1))
      = (∑ i ∈ Finset.range 163, stT142 (i+1)) + stT142 164 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 163
    simpa using h
  have hprev := st142_p163
  have hstep := st142_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p165 : ((16296997868719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT142 (i+1))
      = (∑ i ∈ Finset.range 164, stT142 (i+1)) + stT142 165 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 164
    simpa using h
  have hprev := st142_p164
  have hstep := st142_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p166 : ((3968716797823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT142 (i+1))
      = (∑ i ∈ Finset.range 165, stT142 (i+1)) + stT142 166 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 165
    simpa using h
  have hprev := st142_p165
  have hstep := st142_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p167 : ((16087098208741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT142 (i+1))
      = (∑ i ∈ Finset.range 166, stT142 (i+1)) + stT142 167 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 166
    simpa using h
  have hprev := st142_p166
  have hstep := st142_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p168 : ((3356676582413/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT142 (i+1))
      = (∑ i ∈ Finset.range 167, stT142 (i+1)) + stT142 168 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 167
    simpa using h
  have hprev := st142_p167
  have hstep := st142_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p169 : ((3498515363651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT142 (i+1))
      = (∑ i ∈ Finset.range 168, stT142 (i+1)) + stT142 169 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 168
    simpa using h
  have hprev := st142_p168
  have hstep := st142_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p170 : ((17745028387603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT142 (i+1))
      = (∑ i ∈ Finset.range 169, stT142 (i+1)) + stT142 170 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 169
    simpa using h
  have hprev := st142_p169
  have hstep := st142_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p171 : ((17380123121603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT142 (i+1))
      = (∑ i ∈ Finset.range 170, stT142 (i+1)) + stT142 171 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 170
    simpa using h
  have hprev := st142_p170
  have hstep := st142_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p172 : ((4160110406171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT142 (i+1))
      = (∑ i ∈ Finset.range 171, stT142 (i+1)) + stT142 172 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 171
    simpa using h
  have hprev := st142_p171
  have hstep := st142_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p173 : ((125027508997/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT142 (i+1))
      = (∑ i ∈ Finset.range 172, stT142 (i+1)) + stT142 173 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 172
    simpa using h
  have hprev := st142_p172
  have hstep := st142_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p174 : ((3967949225443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT142 (i+1))
      = (∑ i ∈ Finset.range 173, stT142 (i+1)) + stT142 174 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 173
    simpa using h
  have hprev := st142_p173
  have hstep := st142_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p175 : ((4080672830839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT142 (i+1))
      = (∑ i ∈ Finset.range 174, stT142 (i+1)) + stT142 175 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 174
    simpa using h
  have hprev := st142_p174
  have hstep := st142_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p176 : ((8535391034173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT142 (i+1))
      = (∑ i ∈ Finset.range 175, stT142 (i+1)) + stT142 176 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 175
    simpa using h
  have hprev := st142_p175
  have hstep := st142_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p177 : ((1765424276597/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT142 (i+1))
      = (∑ i ∈ Finset.range 176, stT142 (i+1)) + stT142 177 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 176
    simpa using h
  have hprev := st142_p176
  have hstep := st142_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p178 : ((17720650463039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT142 (i+1))
      = (∑ i ∈ Finset.range 177, stT142 (i+1)) + stT142 178 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 177
    simpa using h
  have hprev := st142_p177
  have hstep := st142_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p179 : ((689409903447/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT142 (i+1))
      = (∑ i ∈ Finset.range 178, stT142 (i+1)) + stT142 179 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 178
    simpa using h
  have hprev := st142_p178
  have hstep := st142_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p180 : ((3298367393067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT142 (i+1))
      = (∑ i ∈ Finset.range 179, stT142 (i+1)) + stT142 180 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 179
    simpa using h
  have hprev := st142_p179
  have hstep := st142_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p181 : ((1592993642043/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT142 (i+1))
      = (∑ i ∈ Finset.range 180, stT142 (i+1)) + stT142 181 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 180
    simpa using h
  have hprev := st142_p180
  have hstep := st142_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p182 : ((1587459617793/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT142 (i+1))
      = (∑ i ∈ Finset.range 181, stT142 (i+1)) + stT142 182 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 181
    simpa using h
  have hprev := st142_p181
  have hstep := st142_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p183 : ((16352704361763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT142 (i+1))
      = (∑ i ∈ Finset.range 182, stT142 (i+1)) + stT142 183 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 182
    simpa using h
  have hprev := st142_p182
  have hstep := st142_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p184 : ((3417330684713/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT142 (i+1))
      = (∑ i ∈ Finset.range 183, stT142 (i+1)) + stT142 184 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 183
    simpa using h
  have hprev := st142_p183
  have hstep := st142_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p185 : ((17660091670219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT142 (i+1))
      = (∑ i ∈ Finset.range 184, stT142 (i+1)) + stT142 185 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 184
    simpa using h
  have hprev := st142_p184
  have hstep := st142_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p186 : ((8877259203377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT142 (i+1))
      = (∑ i ∈ Finset.range 185, stT142 (i+1)) + stT142 186 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 185
    simpa using h
  have hprev := st142_p185
  have hstep := st142_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p187 : ((4330587306667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT142 (i+1))
      = (∑ i ∈ Finset.range 186, stT142 (i+1)) + stT142 187 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 186
    simpa using h
  have hprev := st142_p186
  have hstep := st142_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p188 : ((2075616945321/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT142 (i+1))
      = (∑ i ∈ Finset.range 187, stT142 (i+1)) + stT142 188 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 187
    simpa using h
  have hprev := st142_p187
  have hstep := st142_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p189 : ((1999165031449/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT142 (i+1))
      = (∑ i ∈ Finset.range 188, stT142 (i+1)) + stT142 189 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 188
    simpa using h
  have hprev := st142_p188
  have hstep := st142_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p190 : ((15814225371987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT142 (i+1))
      = (∑ i ∈ Finset.range 189, stT142 (i+1)) + stT142 190 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 189
    simpa using h
  have hprev := st142_p189
  have hstep := st142_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p191 : ((16158560490681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT142 (i+1))
      = (∑ i ∈ Finset.range 190, stT142 (i+1)) + stT142 191 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 190
    simpa using h
  have hprev := st142_p190
  have hstep := st142_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p192 : ((16840504187591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT142 (i+1))
      = (∑ i ∈ Finset.range 191, stT142 (i+1)) + stT142 192 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 191
    simpa using h
  have hprev := st142_p191
  have hstep := st142_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p193 : ((17502222918941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT142 (i+1))
      = (∑ i ∈ Finset.range 192, stT142 (i+1)) + stT142 193 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 192
    simpa using h
  have hprev := st142_p192
  have hstep := st142_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p194 : ((17803141373439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT142 (i+1))
      = (∑ i ∈ Finset.range 193, stT142 (i+1)) + stT142 194 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 193
    simpa using h
  have hprev := st142_p193
  have hstep := st142_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p195 : ((8796582856857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT142 (i+1))
      = (∑ i ∈ Finset.range 194, stT142 (i+1)) + stT142 195 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 194
    simpa using h
  have hprev := st142_p194
  have hstep := st142_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p196 : ((1061439672211/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT142 (i+1))
      = (∑ i ∈ Finset.range 195, stT142 (i+1)) + stT142 196 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 195
    simpa using h
  have hprev := st142_p195
  have hstep := st142_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p197 : ((2035187701271/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT142 (i+1))
      = (∑ i ∈ Finset.range 196, stT142 (i+1)) + stT142 197 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 196
    simpa using h
  have hprev := st142_p196
  have hstep := st142_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p198 : ((7918388202779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT142 (i+1))
      = (∑ i ∈ Finset.range 197, stT142 (i+1)) + stT142 198 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 197
    simpa using h
  have hprev := st142_p197
  have hstep := st142_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p199 : ((7932295030237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT142 (i+1))
      = (∑ i ∈ Finset.range 198, stT142 (i+1)) + stT142 199 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 198
    simpa using h
  have hprev := st142_p198
  have hstep := st142_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p200 : ((8173549697953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT142 (i+1))
      = (∑ i ∈ Finset.range 199, stT142 (i+1)) + stT142 200 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 199
    simpa using h
  have hprev := st142_p199
  have hstep := st142_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p201 : ((1065501896681/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT142 (i+1))
      = (∑ i ∈ Finset.range 200, stT142 (i+1)) + stT142 201 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 200
    simpa using h
  have hprev := st142_p200
  have hstep := st142_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p202 : ((2203922475651/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT142 (i+1))
      = (∑ i ∈ Finset.range 201, stT142 (i+1)) + stT142 202 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 201
    simpa using h
  have hprev := st142_p201
  have hstep := st142_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p203 : ((8911419317301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT142 (i+1))
      = (∑ i ∈ Finset.range 202, stT142 (i+1)) + stT142 203 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 202
    simpa using h
  have hprev := st142_p202
  have hstep := st142_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p204 : ((1753638854699/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT142 (i+1))
      = (∑ i ∈ Finset.range 203, stT142 (i+1)) + stT142 204 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 203
    simpa using h
  have hprev := st142_p203
  have hstep := st142_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p205 : ((3381794103783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT142 (i+1))
      = (∑ i ∈ Finset.range 204, stT142 (i+1)) + stT142 205 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 204
    simpa using h
  have hprev := st142_p204
  have hstep := st142_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p206 : ((16231519329099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT142 (i+1))
      = (∑ i ∈ Finset.range 205, stT142 (i+1)) + stT142 206 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 205
    simpa using h
  have hprev := st142_p205
  have hstep := st142_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p207 : ((7906224285093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT142 (i+1))
      = (∑ i ∈ Finset.range 206, stT142 (i+1)) + stT142 207 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 206
    simpa using h
  have hprev := st142_p206
  have hstep := st142_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p208 : ((15838219238811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT142 (i+1))
      = (∑ i ∈ Finset.range 207, stT142 (i+1)) + stT142 208 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 207
    simpa using h
  have hprev := st142_p207
  have hstep := st142_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p209 : ((16293398177941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT142 (i+1))
      = (∑ i ∈ Finset.range 208, stT142 (i+1)) + stT142 209 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 208
    simpa using h
  have hprev := st142_p208
  have hstep := st142_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p210 : ((16972924505261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT142 (i+1))
      = (∑ i ∈ Finset.range 209, stT142 (i+1)) + stT142 210 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 209
    simpa using h
  have hprev := st142_p209
  have hstep := st142_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p211 : ((17577081345353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT142 (i+1))
      = (∑ i ∈ Finset.range 210, stT142 (i+1)) + stT142 211 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 210
    simpa using h
  have hprev := st142_p210
  have hstep := st142_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p212 : ((17844198560411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT142 (i+1))
      = (∑ i ∈ Finset.range 211, stT142 (i+1)) + stT142 212 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 211
    simpa using h
  have hprev := st142_p211
  have hstep := st142_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p213 : ((2207781427223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT142 (i+1))
      = (∑ i ∈ Finset.range 212, stT142 (i+1)) + stT142 213 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 212
    simpa using h
  have hprev := st142_p212
  have hstep := st142_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p214 : ((8556340201163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT142 (i+1))
      = (∑ i ∈ Finset.range 213, stT142 (i+1)) + stT142 214 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 213
    simpa using h
  have hprev := st142_p213
  have hstep := st142_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p215 : ((16430864767011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT142 (i+1))
      = (∑ i ∈ Finset.range 214, stT142 (i+1)) + stT142 215 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 214
    simpa using h
  have hprev := st142_p214
  have hstep := st142_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p216 : ((15903463628159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT142 (i+1))
      = (∑ i ∈ Finset.range 215, stT142 (i+1)) + stT142 216 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 215
    simpa using h
  have hprev := st142_p215
  have hstep := st142_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p217 : ((15748047496169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT142 (i+1))
      = (∑ i ∈ Finset.range 216, stT142 (i+1)) + stT142 217 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 216
    simpa using h
  have hprev := st142_p216
  have hstep := st142_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p218 : ((16025379448829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT142 (i+1))
      = (∑ i ∈ Finset.range 217, stT142 (i+1)) + stT142 218 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 217
    simpa using h
  have hprev := st142_p217
  have hstep := st142_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p219 : ((16618694103991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT142 (i+1))
      = (∑ i ∈ Finset.range 218, stT142 (i+1)) + stT142 219 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 218
    simpa using h
  have hprev := st142_p218
  have hstep := st142_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p220 : ((8642746884983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT142 (i+1))
      = (∑ i ∈ Finset.range 219, stT142 (i+1)) + stT142 220 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 219
    simpa using h
  have hprev := st142_p219
  have hstep := st142_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p221 : ((8878991982071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT142 (i+1))
      = (∑ i ∈ Finset.range 220, stT142 (i+1)) + stT142 221 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 220
    simpa using h
  have hprev := st142_p220
  have hstep := st142_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p222 : ((8925062143379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT142 (i+1))
      = (∑ i ∈ Finset.range 221, stT142 (i+1)) + stT142 222 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 221
    simpa using h
  have hprev := st142_p221
  have hstep := st142_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p223 : ((2191098673251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT142 (i+1))
      = (∑ i ∈ Finset.range 222, stT142 (i+1)) + stT142 223 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 222
    simpa using h
  have hprev := st142_p222
  have hstep := st142_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p224 : ((8461415250549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT142 (i+1))
      = (∑ i ∈ Finset.range 223, stT142 (i+1)) + stT142 224 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 223
    simpa using h
  have hprev := st142_p223
  have hstep := st142_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p225 : ((8134545753781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT142 (i+1))
      = (∑ i ∈ Finset.range 224, stT142 (i+1)) + stT142 225 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 224
    simpa using h
  have hprev := st142_p224
  have hstep := st142_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p226 : ((7909386582573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT142 (i+1))
      = (∑ i ∈ Finset.range 225, stT142 (i+1)) + stT142 226 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 225
    simpa using h
  have hprev := st142_p225
  have hstep := st142_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p227 : ((7870748885499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT142 (i+1))
      = (∑ i ∈ Finset.range 226, stT142 (i+1)) + stT142 227 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 226
    simpa using h
  have hprev := st142_p226
  have hstep := st142_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p228 : ((8031670914041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT142 (i+1))
      = (∑ i ∈ Finset.range 227, stT142 (i+1)) + stT142 228 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 227
    simpa using h
  have hprev := st142_p227
  have hstep := st142_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p229 : ((8330336860593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT142 (i+1))
      = (∑ i ∈ Finset.range 228, stT142 (i+1)) + stT142 229 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 228
    simpa using h
  have hprev := st142_p228
  have hstep := st142_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p230 : ((8654863915193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT142 (i+1))
      = (∑ i ∈ Finset.range 229, stT142 (i+1)) + stT142 230 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 229
    simpa using h
  have hprev := st142_p229
  have hstep := st142_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p231 : ((4442849393041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT142 (i+1))
      = (∑ i ∈ Finset.range 230, stT142 (i+1)) + stT142 231 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 230
    simpa using h
  have hprev := st142_p230
  have hstep := st142_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p232 : ((1117427316523/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT142 (i+1))
      = (∑ i ∈ Finset.range 231, stT142 (i+1)) + stT142 232 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 231
    simpa using h
  have hprev := st142_p231
  have hstep := st142_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p233 : ((4399005551803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT142 (i+1))
      = (∑ i ∈ Finset.range 232, stT142 (i+1)) + stT142 233 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 232
    simpa using h
  have hprev := st142_p232
  have hstep := st142_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p234 : ((17027490859327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT142 (i+1))
      = (∑ i ∈ Finset.range 233, stT142 (i+1)) + stT142 234 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 233
    simpa using h
  have hprev := st142_p233
  have hstep := st142_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p235 : ((1637772355531/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT142 (i+1))
      = (∑ i ∈ Finset.range 234, stT142 (i+1)) + stT142 235 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 234
    simpa using h
  have hprev := st142_p234
  have hstep := st142_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p236 : ((635062361879/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT142 (i+1))
      = (∑ i ∈ Finset.range 235, stT142 (i+1)) + stT142 236 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 235
    simpa using h
  have hprev := st142_p235
  have hstep := st142_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p237 : ((3139628590843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT142 (i+1))
      = (∑ i ∈ Finset.range 236, stT142 (i+1)) + stT142 237 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 236
    simpa using h
  have hprev := st142_p236
  have hstep := st142_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p238 : ((3975457107777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT142 (i+1))
      = (∑ i ∈ Finset.range 237, stT142 (i+1)) + stT142 238 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 237
    simpa using h
  have hprev := st142_p237
  have hstep := st142_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p239 : ((4103624467909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT142 (i+1))
      = (∑ i ∈ Finset.range 238, stT142 (i+1)) + stT142 239 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 238
    simpa using h
  have hprev := st142_p238
  have hstep := st142_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p240 : ((17058690322199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT142 (i+1))
      = (∑ i ∈ Finset.range 239, stT142 (i+1)) + stT142 240 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 239
    simpa using h
  have hprev := st142_p239
  have hstep := st142_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p241 : ((17615208254243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT142 (i+1))
      = (∑ i ∈ Finset.range 240, stT142 (i+1)) + stT142 241 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 240
    simpa using h
  have hprev := st142_p240
  have hstep := st142_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p242 : ((17897768614507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT142 (i+1))
      = (∑ i ∈ Finset.range 241, stT142 (i+1)) + stT142 242 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 241
    simpa using h
  have hprev := st142_p241
  have hstep := st142_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p243 : ((17814322164427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT142 (i+1))
      = (∑ i ∈ Finset.range 242, stT142 (i+1)) + stT142 243 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 242
    simpa using h
  have hprev := st142_p242
  have hstep := st142_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p244 : ((4348816986643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT142 (i+1))
      = (∑ i ∈ Finset.range 243, stT142 (i+1)) + stT142 244 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 243
    simpa using h
  have hprev := st142_p243
  have hstep := st142_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p245 : ((8390309220083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT142 (i+1))
      = (∑ i ∈ Finset.range 244, stT142 (i+1)) + stT142 245 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 244
    simpa using h
  have hprev := st142_p244
  have hstep := st142_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p246 : ((126342625743/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT142 (i+1))
      = (∑ i ∈ Finset.range 245, stT142 (i+1)) + stT142 246 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 245
    simpa using h
  have hprev := st142_p245
  have hstep := st142_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p247 : ((3941361398691/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT142 (i+1))
      = (∑ i ∈ Finset.range 246, stT142 (i+1)) + stT142 247 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 246
    simpa using h
  have hprev := st142_p246
  have hstep := st142_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p248 : ((7845001832979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT142 (i+1))
      = (∑ i ∈ Finset.range 247, stT142 (i+1)) + stT142 248 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 247
    simpa using h
  have hprev := st142_p247
  have hstep := st142_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p249 : ((7983490172423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT142 (i+1))
      = (∑ i ∈ Finset.range 248, stT142 (i+1)) + stT142 249 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 248
    simpa using h
  have hprev := st142_p248
  have hstep := st142_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_p250 : ((16506376548601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT142 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT142 (i+1))
      = (∑ i ∈ Finset.range 249, stT142 (i+1)) + stT142 250 := by
    have h := Finset.sum_range_succ (fun i => stT142 (i+1)) 249
    simpa using h
  have hprev := st142_p249
  have hstep := st142_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st142_s250 :
    |Real.sin (((142 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))
      - ((-522057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1373151/10000000) (δ := 7199/1000000000) (ψ := -100181/125000) 142 125
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 142`** (evaluated boundary). -/
theorem station_142_sign : 0 < hardyG ((((142:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 142 250 (by norm_num) (by norm_num)
    ((-100181/125000 : ℚ) : ℝ)
  have hchain := st142_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT142 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((142 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-100181/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st142_c250
  have hsinb := abs_le.mp st142_s250
  have hbdy_lo : ((18644397342257/322628000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((142 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-100181/125000 : ℚ) : ℝ))) / 2
          - ((((142:ℕ)):ℝ))
            * Real.sin (((142 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-100181/125000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((142:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((142:ℝ) * Real.log (250:ℝ) - ((-100181/125000 : ℚ) : ℝ))) / 2
        - ((142:ℝ)) * Real.sin ((142:ℝ) * Real.log (250:ℝ) - ((-100181/125000 : ℚ) : ℝ))
        ≥ ((147397027/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((142:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((147397027/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((147397027/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((147397027/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((142:ℕ)):ℝ))+1) * (((((142:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((4573684621/9765625000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((16506376548601/10000000000000 : ℚ) : ℝ) + ((18644397342257/322628000000000 : ℚ) : ℝ)
      - ((4573684621/9765625000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-100181/125000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((142:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-100181/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((142:ℕ)):ℝ)))).re
      - Real.sin ((-100181/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((142:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((142:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((142:ℕ)):ℝ))
      = (((((142:ℕ)):ℝ)) * (Real.log ((((142:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((142:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_142
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
  have hθwin : |(((-100181/125000 : ℚ) : ℝ) + ((24:ℤ)) * (2*Real.pi)) - theta ((((142:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((142:ℕ)):ℝ)))
    (φ := ((-100181/125000 : ℚ) : ℝ) + ((24:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-100181/125000 : ℚ)) : ℝ) 24).1,
    (cos_sin_shift (((-100181/125000 : ℚ)) : ℝ) 24).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_142_sign
end AxiomAudit
