import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 106` (rung-109; evaluated boundary, N = 200)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT106 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((106 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))

theorem st106_c1 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((258657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2567717/10000000) (δ := 21/100000000) (ψ := -1027087/1000000) 106 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t1 : ((32329/62500 : ℚ) : ℝ) ≤ stT106 1 := by
  have hc : ((32329/62500 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32329/62500 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((32329/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c2 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((623539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2243839/10000000) (δ := 17/2000000) (ψ := -1027087/1000000) 106 12
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t2 : ((4408732492763/10000000000000 : ℚ) : ℝ) ≤ stT106 2 := by
  have hc : ((623489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4408732492763/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((623489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c3 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-323793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4751329/10000000) (δ := 181/20000000) (ψ := -1027087/1000000) 106 19
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t3 : ((-1869708532029/10000000000000 : ℚ) : ℝ) ≤ stT106 3 := by
  have hc : ((-323843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1869708532029/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-323843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c4 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-949413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1763849/2500000) (δ := 619/100000000) (ψ := -1027087/1000000) 106 24
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t4 : ((-4747315949463/10000000000000 : ℚ) : ℝ) ≤ stT106 4 := by
  have hc : ((-949463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4747315949463/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-949463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c5 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-399257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1238439/2500000) (δ := 233/25000000) (ψ := -1027087/1000000) 106 27
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t5 : ((-223219401219/1250000000000 : ℚ) : ℝ) ≤ stT106 5 := by
  have hc : ((-399307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223219401219/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-399307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c6 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-24229/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3072539/5000000) (δ := 703/100000000) (ψ := -1027087/1000000) 106 30
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t6 : ((-1582733751787/5000000000000 : ℚ) : ℝ) ≤ stT106 6 := by
  have hc : ((-387689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1582733751787/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-387689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c7 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((998671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128881/10000000) (δ := 137/25000000) (ψ := -1027087/1000000) 106 33
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t7 : ((943607967731/2500000000000 : ℚ) : ℝ) ≤ stT106 7 := by
  have hc : ((998621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((943607967731/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((998621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c8 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((6877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3841011/10000000) (δ := 323/50000000) (ψ := -1027087/1000000) 106 35
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t8 : ((24278505111/2000000000000 : ℚ) : ℝ) ≤ stT106 8 := by
  have hc : ((6867/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24278505111/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((6867/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c9 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((57751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3637589/10000000) (δ := 399/50000000) (ψ := -1027087/1000000) 106 37
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t9 : ((96209990379/2500000000000 : ℚ) : ℝ) ≤ stT106 9 := by
  have hc : ((28863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96209990379/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((28863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c10 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((998383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142199/10000000) (δ := 3/312500) (ψ := -1027087/1000000) 106 39
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t10 : ((3157005484241/10000000000000 : ℚ) : ℝ) ≤ stT106 10 := by
  have hc : ((998333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3157005484241/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((998333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c11 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-185461/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601653/1000000) (δ := 741/100000000) (ψ := -1027087/1000000) 106 41
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t11 : ((-559223746479/2500000000000 : ℚ) : ℝ) ≤ stT106 11 := by
  have hc : ((-370947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-559223746479/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-370947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c12 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((861079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 666761/5000000) (δ := 551/100000000) (ψ := -1027087/1000000) 106 42
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t12 : ((2485576326779/10000000000000 : ℚ) : ℝ) ≤ stT106 12 := by
  have hc : ((861029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2485576326779/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((861029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c13 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-7347/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1709219/2500000) (δ := 291/50000000) (ψ := -1027087/1000000) 106 43
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t13 : ((-101890106237/400000000000 : ℚ) : ℝ) ≤ stT106 13 := by
  have hc : ((-36737/40000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101890106237/400000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-36737/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c14 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-394367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2470219/5000000) (δ := 779/100000000) (ψ := -1027087/1000000) 106 45
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t14 : ((-1054124001621/10000000000000 : ℚ) : ℝ) ≤ stT106 14 := by
  have hc : ((-394417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1054124001621/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-394417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c15 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((292419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236529/1000000) (δ := 267/25000000) (ψ := -1027087/1000000) 106 46
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t15 : ((94369724909/625000000000 : ℚ) : ℝ) ≤ stT106 15 := by
  have hc : ((146197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94369724909/625000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((146197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c16 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((185117/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194109/2000000) (δ := 419/50000000) (ψ := -1027087/1000000) 106 47
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t16 : ((185107/800000 : ℚ) : ℝ) ≤ stT106 16 := by
  have hc : ((185107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185107/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((185107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c17 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((97009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76623/1250000) (δ := 627/100000000) (ψ := -1027087/1000000) 106 48
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t17 : ((14704327089/62500000000 : ℚ) : ℝ) ≤ stT106 17 := by
  have hc : ((24251/25000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14704327089/62500000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((24251/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c18 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((178351/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1173967/10000000) (δ := 607/100000000) (ψ := -1027087/1000000) 106 49
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t18 : ((210176830251/1000000000000 : ℚ) : ℝ) ≤ stT106 18 := by
  have hc : ((178341/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210176830251/1000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((178341/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c19 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((260981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2554117/10000000) (δ := 817/100000000) (ψ := -1027087/1000000) 106 50
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t19 : ((149668508523/1250000000000 : ℚ) : ℝ) ≤ stT106 19 := by
  have hc : ((65239/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149668508523/1250000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((65239/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c20 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-146301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4669357/10000000) (δ := 3/390625) (ψ := -1027087/1000000) 106 51
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t20 : ((-40899360771/625000000000 : ℚ) : ℝ) ≤ stT106 20 := by
  have hc : ((-73163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40899360771/625000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-73163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c21 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-986839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7447927/10000000) (δ := 171/25000000) (ψ := -1027087/1000000) 106 52
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t21 : ((-2153568451131/10000000000000 : ℚ) : ℝ) ≤ stT106 21 := by
  have hc : ((-986889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2153568451131/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-986889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c22 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-46499/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4879877/10000000) (δ := 539/100000000) (ψ := -1027087/1000000) 106 52
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t22 : ((-49574782521/625000000000 : ℚ) : ℝ) ≤ stT106 22 := by
  have hc : ((-186021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49574782521/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-186021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c23 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((464211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 951631/10000000) (δ := 913/100000000) (ψ := -1027087/1000000) 106 53
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t23 : ((60493415799/312500000000 : ℚ) : ℝ) ≤ stT106 23 := by
  have hc : ((232093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60493415799/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((232093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c24 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((178619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1739017/5000000) (δ := 743/100000000) (ψ := -1027087/1000000) 106 54
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t24 : ((364502364129/10000000000000 : ℚ) : ℝ) ≤ stT106 24 := by
  have hc : ((178569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364502364129/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((178569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c25 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-978923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3669897/5000000) (δ := 823/100000000) (ψ := -1027087/1000000) 106 54
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t25 : ((-1957946978973/10000000000000 : ℚ) : ℝ) ≤ stT106 25 := by
  have hc : ((-978973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1957946978973/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-978973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c26 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((344703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50633/250000) (δ := 21/3125000) (ψ := -1027087/1000000) 106 55
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t26 : ((337984525579/2500000000000 : ℚ) : ℝ) ≤ stT106 26 := by
  have hc : ((172339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337984525579/2500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((172339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c27 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((12257/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3681457/10000000) (δ := 331/50000000) (ψ := -1027087/1000000) 106 56
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t27 : ((188612547/10000000000 : ℚ) : ℝ) ≤ stT106 27 := by
  have hc : ((49003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188612547/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((49003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c28 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-725383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5955969/10000000) (δ := 981/100000000) (ψ := -1027087/1000000) 106 56
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t28 : ((-1370939968359/10000000000000 : ℚ) : ℝ) ≤ stT106 28 := by
  have hc : ((-725433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1370939968359/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-725433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c29 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((983643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226397/5000000) (δ := 751/100000000) (ψ := -1027087/1000000) 106 57
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t29 : ((1826485972129/10000000000000 : ℚ) : ℝ) ≤ stT106 29 := by
  have hc : ((983593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1826485972129/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((983593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c30 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-963543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3588423/5000000) (δ := 863/100000000) (ψ := -1027087/1000000) 106 58
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t30 : ((-879636105503/5000000000000 : ℚ) : ℝ) ≤ stT106 30 := by
  have hc : ((-963593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-879636105503/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-963593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c31 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((51407/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1512457/10000000) (δ := 51/5000000) (ψ := -1027087/1000000) 106 58
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t31 : ((738592671243/5000000000000 : ℚ) : ℝ) ≤ stT106 31 := by
  have hc : ((411231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((738592671243/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((411231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c32 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-168949/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2891051/5000000) (δ := 1069/100000000) (ψ := -1027087/1000000) 106 59
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t32 : ((-597369127941/5000000000000 : ℚ) : ℝ) ≤ stT106 32 := by
  have hc : ((-337923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-597369127941/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-337923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c33 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((582533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 593097/2500000) (δ := 317/50000000) (ψ := -1027087/1000000) 106 59
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t33 : ((126746553351/1250000000000 : ℚ) : ℝ) ≤ stT106 33 := by
  have hc : ((582483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126746553351/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((582483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c34 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-563833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -271227/500000) (δ := 409/50000000) (ψ := -1027087/1000000) 106 60
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t34 : ((-483525725319/5000000000000 : ℚ) : ℝ) ≤ stT106 34 := by
  have hc : ((-563883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483525725319/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-563883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c35 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((123873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2257157/10000000) (δ := 1/160000) (ψ := -1027087/1000000) 106 60
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t35 : ((52341654951/500000000000 : ℚ) : ℝ) ≤ stT106 35 := by
  have hc : ((123863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52341654951/500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((123863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c36 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-73347/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1496381/2500000) (δ := 43/6250000) (ψ := -1027087/1000000) 106 61
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t36 : ((-15281669723/125000000000 : ℚ) : ℝ) ≤ stT106 36 := by
  have hc : ((-9169/12500 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15281669723/125000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-9169/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c37 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((13636/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255041/2000000) (δ := 29/3125000) (ψ := -1027087/1000000) 106 61
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t37 : ((717316788403/5000000000000 : ℚ) : ℝ) ≤ stT106 37 := by
  have hc : ((436327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((717316788403/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((436327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c38 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-196197/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7365673/10000000) (δ := 313/50000000) (ψ := -1027087/1000000) 106 62
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t38 : ((-63657987701/400000000000 : ℚ) : ℝ) ≤ stT106 38 := by
  have hc : ((-196207/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63657987701/400000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-196207/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c39 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((981459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482169/10000000) (δ := 577/100000000) (ψ := -1027087/1000000) 106 62
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t39 : ((1571511584929/10000000000000 : ℚ) : ℝ) ≤ stT106 39 := by
  have hc : ((981409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1571511584929/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((981409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c40 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-24863/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124541/200000) (δ := 283/50000000) (ψ := -1027087/1000000) 106 62
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t40 : ((-629029271787/5000000000000 : ℚ) : ℝ) ≤ stT106 40 := by
  have hc : ((-397833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629029271787/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-397833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c41 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((385591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2937371/10000000) (δ := 697/100000000) (ψ := -1027087/1000000) 106 63
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t41 : ((602113644717/10000000000000 : ℚ) : ℝ) ≤ stT106 41 := by
  have hc : ((385541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((602113644717/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((385541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c42 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((95119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21553/62500) (δ := 443/50000000) (ψ := -1027087/1000000) 106 63
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t42 : ((73366590051/2500000000000 : ℚ) : ℝ) ≤ stT106 42 := by
  have hc : ((47547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73366590051/2500000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((47547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c43 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-371909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6023901/10000000) (δ := 7/781250) (ψ := -1027087/1000000) 106 64
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t43 : ((-141798535731/1250000000000 : ℚ) : ℝ) ≤ stT106 43 := by
  have hc : ((-185967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141798535731/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-185967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c44 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((999627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68321/10000000) (δ := 179/25000000) (ψ := -1027087/1000000) 106 64
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t44 : ((376729575953/2500000000000 : ℚ) : ℝ) ≤ stT106 44 := by
  have hc : ((999577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376729575953/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((999577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c45 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-148749/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1505907/2500000) (δ := 947/100000000) (ψ := -1027087/1000000) 106 64
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t45 : ((-27719603301/250000000000 : ℚ) : ℝ) ≤ stT106 45 := by
  have hc : ((-148759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27719603301/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-148759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c46 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((26823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154397/400000) (δ := 509/50000000) (ψ := -1027087/1000000) 106 65
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t46 : ((39474619887/10000000000000 : ℚ) : ℝ) ≤ stT106 46 := by
  have hc : ((26773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39474619887/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((26773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c47 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((741369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1839219/10000000) (δ := 213/20000000) (ψ := -1027087/1000000) 106 65
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t47 : ((1081324218031/10000000000000 : ℚ) : ℝ) ≤ stT106 47 := by
  have hc : ((741319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1081324218031/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((741319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c48 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-492429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1854593/2500000) (δ := 197/20000000) (ψ := -1027087/1000000) 106 65
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t48 : ((-22212383897/156250000000 : ℚ) : ℝ) ≤ stT106 48 := by
  have hc : ((-246227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22212383897/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-246227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c49 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((213243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70637/250000) (δ := 1009/100000000) (ψ := -1027087/1000000) 106 66
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t49 : ((152298525739/2500000000000 : ℚ) : ℝ) ≤ stT106 49 := by
  have hc : ((106609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152298525739/2500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((106609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c50 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((530763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1264119/5000000) (δ := 507/50000000) (ψ := -1027087/1000000) 106 66
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t50 : ((750541223869/10000000000000 : ℚ) : ℝ) ≤ stT106 50 := by
  have hc : ((530713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((750541223869/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((530713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c51 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-999513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3887967/5000000) (δ := 367/50000000) (ψ := -1027087/1000000) 106 66
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t51 : ((-1399669077203/10000000000000 : ℚ) : ℝ) ≤ stT106 51 := by
  have hc : ((-999563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1399669077203/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-999563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c52 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((440631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2786237/10000000) (δ := 903/100000000) (ψ := -1027087/1000000) 106 67
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t52 : ((2443902807/40000000000 : ℚ) : ℝ) ≤ stT106 52 := by
  have hc : ((440581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2443902807/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((440581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c53 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((617989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452307/2000000) (δ := 943/100000000) (ψ := -1027087/1000000) 106 67
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t53 : ((169760820019/2000000000000 : ℚ) : ℝ) ≤ stT106 53 := by
  have hc : ((617939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169760820019/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((617939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c54 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-967509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144299/200000) (δ := 603/100000000) (ψ := -1027087/1000000) 106 67
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t54 : ((-329170344713/2500000000000 : ℚ) : ℝ) ≤ stT106 54 := by
  have hc : ((-967559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-329170344713/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-967559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c55 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((59161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3630491/10000000) (δ := 89/10000000) (ψ := -1027087/1000000) 106 68
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t55 : ((311480169/19531250000 : ℚ) : ℝ) ≤ stT106 55 := by
  have hc : ((1848/15625 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311480169/19531250000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((1848/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c56 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((448521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1144413/10000000) (δ := 19/2000000) (ψ := -1027087/1000000) 106 68
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t56 : ((18728996743/156250000000 : ℚ) : ℝ) ≤ stT106 56 := by
  have hc : ((28031/31250 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18728996743/156250000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((28031/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c57 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-691183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5834801/10000000) (δ := 71/10000000) (ψ := -1027087/1000000) 106 68
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t57 : ((-915560919189/10000000000000 : ℚ) : ℝ) ≤ stT106 57 := by
  have hc : ((-691233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-915560919189/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-691233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c58 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-509793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5264351/10000000) (δ := 491/50000000) (ψ := -1027087/1000000) 106 69
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t58 : ((-133891399759/2000000000000 : ℚ) : ℝ) ≤ stT106 58 := by
  have hc : ((-509843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133891399759/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-509843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c59 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((95717/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367163/5000000) (δ := 311/50000000) (ψ := -1027087/1000000) 106 69
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t59 : ((3893949999/31250000000 : ℚ) : ℝ) ≤ stT106 59 := by
  have hc : ((2991/3125 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3893949999/31250000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((2991/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c60 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((82877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3719561/10000000) (δ := 661/100000000) (ψ := -1027087/1000000) 106 69
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t60 : ((53464580019/5000000000000 : ℚ) : ℝ) ≤ stT106 60 := by
  have hc : ((82827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53464580019/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((82827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c61 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-995169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3804069/5000000) (δ := 163/25000000) (ψ := -1027087/1000000) 106 70
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t61 : ((-1274247555811/10000000000000 : ℚ) : ℝ) ≤ stT106 61 := by
  have hc : ((-995219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1274247555811/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-995219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c62 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((62131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32991/100000) (δ := 109/12500000) (ψ := -1027087/1000000) 106 70
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t62 : ((157781114237/5000000000000 : ℚ) : ℝ) ≤ stT106 62 := by
  have hc : ((124237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157781114237/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((124237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c63 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((185999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 940991/10000000) (δ := 791/100000000) (ψ := -1027087/1000000) 106 70
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t63 : ((234324007309/2000000000000 : ℚ) : ℝ) ≤ stT106 63 := by
  have hc : ((185989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234324007309/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((185989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c64 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-57159/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1022861/2000000) (δ := 213/25000000) (ψ := -1027087/1000000) 106 70
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t64 : ((-285826478661/5000000000000 : ℚ) : ℝ) ≤ stT106 64 := by
  have hc : ((-228661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285826478661/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-228661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c65 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-853791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6485049/10000000) (δ := 351/50000000) (ψ := -1027087/1000000) 106 71
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t65 : ((-264764994167/2500000000000 : ℚ) : ℝ) ≤ stT106 65 := by
  have hc : ((-853841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264764994167/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-853841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c66 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((70077/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19056/78125) (δ := 621/100000000) (ψ := -1027087/1000000) 106 71
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t66 : ((172502134331/2500000000000 : ℚ) : ℝ) ≤ stT106 66 := by
  have hc : ((280283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172502134331/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((280283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c67 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((814837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1545869/10000000) (δ := 881/100000000) (ψ := -1027087/1000000) 106 71
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t67 : ((497710194589/5000000000000 : ℚ) : ℝ) ≤ stT106 67 := by
  have hc : ((814787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497710194589/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((814787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c68 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-289683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5471867/10000000) (δ := 1021/100000000) (ψ := -1027087/1000000) 106 71
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t68 : ((-87830701933/1250000000000 : ℚ) : ℝ) ≤ stT106 68 := by
  have hc : ((-72427/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87830701933/1250000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-72427/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c69 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-414179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1273483/2000000) (δ := 21/2000000) (ψ := -1027087/1000000) 106 72
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t69 : ((-124660803309/1250000000000 : ℚ) : ℝ) ≤ stT106 69 := by
  have hc : ((-103551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124660803309/1250000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-103551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c70 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((260933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2554399/10000000) (δ := 63/10000000) (ψ := -1027087/1000000) 106 72
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t70 : ((19490284189/312500000000 : ℚ) : ℝ) ≤ stT106 70 := by
  have hc : ((65227/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19490284189/312500000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((65227/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c71 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((886157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1204529/10000000) (δ := 793/100000000) (ψ := -1027087/1000000) 106 72
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t71 : ((1051614951567/10000000000000 : ℚ) : ℝ) ≤ stT106 71 := by
  have hc : ((886107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1051614951567/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((886107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c72 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-95869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4910883/10000000) (δ := 89/10000000) (ψ := -1027087/1000000) 106 72
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t72 : ((-14124687291/312500000000 : ℚ) : ℝ) ≤ stT106 72 := by
  have hc : ((-191763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14124687291/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-191763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c73 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-959703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142837/200000) (δ := 659/100000000) (ψ := -1027087/1000000) 106 73
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t73 : ((-280826607059/2500000000000 : ℚ) : ℝ) ≤ stT106 73 := by
  have hc : ((-959753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280826607059/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-959753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c74 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((7781/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110511/312500) (δ := 241/25000000) (ψ := -1027087/1000000) 106 73
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t74 : ((4521159783/250000000000 : ℚ) : ℝ) ≤ stT106 74 := by
  have hc : ((15557/100000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4521159783/250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((15557/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c75 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((499983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20749/10000000) (δ := 919/100000000) (ψ := -1027087/1000000) 106 73
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t75 : ((2886507513/25000000000 : ℚ) : ℝ) ≤ stT106 75 := by
  have hc : ((249979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2886507513/25000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((249979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c76 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((1973/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1765367/5000000) (δ := 639/100000000) (ψ := -1027087/1000000) 106 73
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t76 : ((9049871881/500000000000 : ℚ) : ℝ) ≤ stT106 76 := by
  have hc : ((15779/100000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9049871881/500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((15779/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c77 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-117691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1398967/2000000) (δ := 859/100000000) (ψ := -1027087/1000000) 106 73
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t77 : ((-268256984567/2500000000000 : ℚ) : ℝ) ≤ stT106 77 := by
  have hc : ((-470789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268256984567/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-470789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c78 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-259933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2646863/5000000) (δ := 101/12500000) (ψ := -1027087/1000000) 106 74
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t78 : ((-73586181081/1250000000000 : ℚ) : ℝ) ≤ stT106 78 := by
  have hc : ((-129979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73586181081/1250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-129979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c79 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((719889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479471/2500000) (δ := 107/20000000) (ψ := -1027087/1000000) 106 74
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t79 : ((809881500993/10000000000000 : ℚ) : ℝ) ≤ stT106 79 := by
  have hc : ((719839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((809881500993/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((719839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c80 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((843947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1415493/10000000) (δ := 91/12500000) (ψ := -1027087/1000000) 106 74
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t80 : ((943504694601/10000000000000 : ℚ) : ℝ) ≤ stT106 80 := by
  have hc : ((843897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((943504694601/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((843897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c81 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-153571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4707461/10000000) (δ := 111/20000000) (ψ := -1027087/1000000) 106 74
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t81 : ((-5333198711/156250000000 : ℚ) : ℝ) ≤ stT106 81 := by
  have hc : ((-38399/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5333198711/156250000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-38399/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c82 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-999117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121077/156250) (δ := 299/50000000) (ψ := -1027087/1000000) 106 75
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t82 : ((-275849026193/2500000000000 : ℚ) : ℝ) ≤ stT106 82 := by
  have hc : ((-999167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275849026193/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-999167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c83 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-241499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4536767/10000000) (δ := 499/50000000) (ψ := -1027087/1000000) 106 75
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t83 : ((-265134569007/10000000000000 : ℚ) : ℝ) ≤ stT106 83 := by
  have hc : ((-241549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265134569007/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-241549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c84 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((26719/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -340769/2500000) (δ := 539/50000000) (ψ := -1027087/1000000) 106 75
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t84 : ((466417634631/5000000000000 : ℚ) : ℝ) ≤ stT106 84 := by
  have hc : ((427479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466417634631/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((427479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c85 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((758869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354611/2000000) (δ := 117/20000000) (ψ := -1027087/1000000) 106 75
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t85 : ((205763636497/2500000000000 : ℚ) : ℝ) ≤ stT106 85 := by
  have hc : ((758819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205763636497/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((758819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c86 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-184627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 974501/2000000) (δ := 197/20000000) (ψ := -1027087/1000000) 106 75
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t86 : ((-6222356933/156250000000 : ℚ) : ℝ) ≤ stT106 86 := by
  have hc : ((-46163/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6222356933/156250000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-46163/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c87 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-49973/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24287/31250) (δ := 887/100000000) (ψ := -1027087/1000000) 106 76
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t87 : ((-107158766463/1000000000000 : ℚ) : ℝ) ≤ stT106 87 := by
  have hc : ((-99951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107158766463/1000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-99951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c88 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-40091/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1185809/2500000) (δ := 947/100000000) (ψ := -1027087/1000000) 106 76
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t88 : ((-42743828889/1250000000000 : ℚ) : ℝ) ≤ stT106 88 := by
  have hc : ((-160389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42743828889/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-160389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c89 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((382569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1748853/10000000) (δ := 23/3125000) (ψ := -1027087/1000000) 106 76
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t89 : ((25343468273/312500000000 : ℚ) : ℝ) ≤ stT106 89 := by
  have hc : ((23909/31250 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25343468273/312500000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((23909/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c90 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((176951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1212071/10000000) (δ := 179/25000000) (ψ := -1027087/1000000) 106 76
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t90 : ((46628023143/500000000000 : ℚ) : ℝ) ≤ stT106 90 := by
  have hc : ((176941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46628023143/500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((176941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c91 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-85211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2070139/5000000) (δ := 279/25000000) (ψ := -1027087/1000000) 106 76
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t91 : ((-17875565477/2000000000000 : ℚ) : ℝ) ≤ stT106 91 := by
  have hc : ((-85261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17875565477/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-85261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c92 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-94701/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3518241/5000000) (δ := 51/6250000) (ψ := -1027087/1000000) 106 76
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t92 : ((-49368959269/500000000000 : ℚ) : ℝ) ≤ stT106 92 := by
  have hc : ((-47353/50000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49368959269/500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-47353/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c93 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-682983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5806589/10000000) (δ := 967/100000000) (ψ := -1027087/1000000) 106 77
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t93 : ((-88534054427/1250000000000 : ℚ) : ℝ) ≤ stT106 93 := by
  have hc : ((-683033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88534054427/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-683033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c94 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((372649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2972337/10000000) (δ := 867/100000000) (ψ := -1027087/1000000) 106 77
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t94 : ((384306433179/10000000000000 : ℚ) : ℝ) ≤ stT106 94 := by
  have hc : ((372599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384306433179/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((372599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c95 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((997741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84039/5000000) (δ := 967/100000000) (ψ := -1027087/1000000) 106 77
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t95 : ((511804508399/5000000000000 : ℚ) : ℝ) ≤ stT106 95 := by
  have hc : ((997691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((511804508399/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((997691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c96 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((503867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81463/312500) (δ := 947/100000000) (ψ := -1027087/1000000) 106 77
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t96 : ((25710285327/500000000000 : ℚ) : ℝ) ≤ stT106 96 := by
  have hc : ((503817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25710285327/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((503817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c97 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-539957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1070591/2000000) (δ := 827/100000000) (ψ := -1027087/1000000) 106 77
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t97 : ((-548294487429/10000000000000 : ℚ) : ℝ) ≤ stT106 97 := by
  have hc : ((-540007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548294487429/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-540007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c98 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-996237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1909259/2500000) (δ := 409/50000000) (ψ := -1027087/1000000) 106 78
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t98 : ((-1006402301911/10000000000000 : ℚ) : ℝ) ≤ stT106 98 := by
  have hc : ((-996287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1006402301911/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-996287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c99 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-99163/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2473329/5000000) (δ := 113/20000000) (ψ := -1027087/1000000) 106 78
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t99 : ((-99675146169/2500000000000 : ℚ) : ℝ) ≤ stT106 99 := by
  have hc : ((-198351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99675146169/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-198351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c100 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((122223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2283319/10000000) (δ := 439/50000000) (ψ := -1027087/1000000) 106 78
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t100 : ((122212877787/2000000000000 : ℚ) : ℝ) ≤ stT106 100 := by
  have hc : ((122213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122212877787/2000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((122213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c101 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((990019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 353519/10000000) (δ := 181/20000000) (ψ := -1027087/1000000) 106 78
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t101 : ((985055783853/10000000000000 : ℚ) : ℝ) ≤ stT106 101 := by
  have hc : ((989969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((985055783853/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((989969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c102 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((375601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1482189/5000000) (δ := 37/4000000) (ψ := -1027087/1000000) 106 78
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t102 : ((371850695997/10000000000000 : ℚ) : ℝ) ≤ stT106 102 := by
  have hc : ((375551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371850695997/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((375551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c103 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-604477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1387441/2500000) (δ := 459/50000000) (ψ := -1027087/1000000) 106 78
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t103 : ((-59565858891/1000000000000 : ℚ) : ℝ) ≤ stT106 103 := by
  have hc : ((-604527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59565858891/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-604527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c104 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-497377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7597793/10000000) (δ := 257/25000000) (ψ := -1027087/1000000) 106 79
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t104 : ((-243871475281/2500000000000 : ℚ) : ℝ) ≤ stT106 104 := by
  have hc : ((-248701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243871475281/2500000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-248701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c105 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-438527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39546/78125) (δ := 107/20000000) (ψ := -1027087/1000000) 106 79
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t105 : ((-428007732877/10000000000000 : ℚ) : ℝ) ≤ stT106 105 := by
  have hc : ((-438577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428007732877/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-438577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c106 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((523359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2550021/10000000) (δ := 247/25000000) (ψ := -1027087/1000000) 106 79
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t106 : ((101656436413/2000000000000 : ℚ) : ℝ) ≤ stT106 106 := by
  have hc : ((523309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101656436413/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((523309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c107 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((199939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3087/500000) (δ := 143/20000000) (ψ := -1027087/1000000) 106 79
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t107 : ((12079910109/125000000000 : ℚ) : ℝ) ≤ stT106 107 := by
  have hc : ((199929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12079910109/125000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((199929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c108 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((572407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1201697/5000000) (δ := 159/20000000) (ψ := -1027087/1000000) 106 79
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t108 : ((2203002093/40000000000 : ℚ) : ℝ) ≤ stT106 108 := by
  have hc : ((572357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2203002093/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((572357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c109 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-359309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 302863/625000) (δ := 217/25000000) (ψ := -1027087/1000000) 106 79
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t109 : ((-344203752893/10000000000000 : ℚ) : ℝ) ≤ stT106 109 := by
  have hc : ((-359359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344203752893/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-359359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c110 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-486231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1816479/2500000) (δ := 43/6250000) (ψ := -1027087/1000000) 106 79
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t110 : ((-28976694033/312500000000 : ℚ) : ℝ) ≤ stT106 110 := by
  have hc : ((-30391/31250 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28976694033/312500000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-30391/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c111 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-5993/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6043841/10000000) (δ := 133/12500000) (ψ := -1027087/1000000) 106 80
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t111 : ((-14221708893/200000000000 : ℚ) : ℝ) ≤ stT106 111 := by
  have hc : ((-29967/40000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14221708893/200000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-29967/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c112 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((12969/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -458393/1250000) (δ := 719/100000000) (ψ := -1027087/1000000) 106 80
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t112 : ((48994580261/5000000000000 : ℚ) : ℝ) ≤ stT106 112 := by
  have hc : ((51851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48994580261/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((51851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c113 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((86551/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -327893/2500000) (δ := 27/3125000) (ψ := -1027087/1000000) 106 80
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t113 : ((508847207/6250000000 : ℚ) : ℝ) ≤ stT106 113 := by
  have hc : ((43273/50000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((508847207/6250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((43273/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c114 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((917401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255811/2500000) (δ := 73/12500000) (ψ := -1027087/1000000) 106 80
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t114 : ((171835437267/2000000000000 : ℚ) : ℝ) ≤ stT106 114 := by
  have hc : ((917351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171835437267/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((917351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c115 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((233551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 333767/1000000) (δ := 191/25000000) (ψ := -1027087/1000000) 106 80
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t115 : ((27217577063/1250000000000 : ℚ) : ℝ) ≤ stT106 115 := by
  have hc : ((233501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27217577063/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((233501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c116 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-630367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 704007/1250000) (δ := 939/100000000) (ψ := -1027087/1000000) 106 80
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t116 : ((-585327684909/10000000000000 : ℚ) : ℝ) ≤ stT106 116 := by
  have hc : ((-630417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-585327684909/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-630417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c117 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-999777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1560243/2000000) (δ := 713/100000000) (ψ := -1027087/1000000) 106 81
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t117 : ((-924341061327/10000000000000 : ℚ) : ℝ) ≤ stT106 117 := by
  have hc : ((-999827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-924341061327/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-999827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c118 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-603239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2772941/5000000) (δ := 813/100000000) (ψ := -1027087/1000000) 106 81
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t118 : ((-22214910847/400000000000 : ℚ) : ℝ) ≤ stT106 118 := by
  have hc : ((-603289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22214910847/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-603289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c119 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((244461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1654791/5000000) (δ := 97/10000000) (ψ := -1027087/1000000) 106 81
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t119 : ((112025537439/5000000000000 : ℚ) : ℝ) ≤ stT106 119 := by
  have hc : ((244411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112025537439/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((244411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c120 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((906111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272999/2500000) (δ := 633/100000000) (ψ := -1027087/1000000) 106 81
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t120 : ((82711590507/1000000000000 : ℚ) : ℝ) ≤ stT106 120 := by
  have hc : ((906061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82711590507/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((906061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c121 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((903523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1107187/10000000) (δ := 593/100000000) (ψ := -1027087/1000000) 106 81
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t121 : ((82133826957/1000000000000 : ℚ) : ℝ) ≤ stT106 121 := by
  have hc : ((903473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82133826957/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((903473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c122 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((126359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3288269/10000000) (δ := 613/100000000) (ψ := -1027087/1000000) 106 81
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t122 : ((57188685619/2500000000000 : ℚ) : ℝ) ≤ stT106 122 := by
  have hc : ((63167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57188685619/2500000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((63167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c123 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-286361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2725773/5000000) (δ := 11/2000000) (ψ := -1027087/1000000) 106 81
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t123 : ((-12911283231/250000000000 : ℚ) : ℝ) ≤ stT106 123 := by
  have hc : ((-143193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12911283231/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-143193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c124 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-497367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7597307/10000000) (δ := 67/10000000) (ψ := -1027087/1000000) 106 81
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t124 : ((-27916965349/312500000000 : ℚ) : ℝ) ≤ stT106 124 := by
  have hc : ((-31087/31250 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27916965349/312500000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-31087/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c125 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-732547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5982131/10000000) (δ := 703/100000000) (ψ := -1027087/1000000) 106 82
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t125 : ((-163813817379/2500000000000 : ℚ) : ℝ) ≤ stT106 125 := by
  have hc : ((-732597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163813817379/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-732597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c126 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((2821/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1935283/5000000) (δ := 1023/100000000) (ψ := -1027087/1000000) 106 82
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t126 : ((1003030533/500000000000 : ℚ) : ℝ) ≤ stT106 126 := by
  have hc : ((11259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1003030533/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((11259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c127 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((758181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1775693/10000000) (δ := 9/1000000) (ψ := -1027087/1000000) 106 82
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t127 : ((168183022909/2500000000000 : ℚ) : ℝ) ≤ stT106 127 := by
  have hc : ((758131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168183022909/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((758131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c128 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((248169/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 302749/10000000) (δ := 33/5000000) (ψ := -1027087/1000000) 106 82
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t128 : ((438682623379/5000000000000 : ℚ) : ℝ) ≤ stT106 128 := by
  have hc : ((496313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438682623379/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((496313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c129 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((584927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295627/1250000) (δ := 1043/100000000) (ψ := -1027087/1000000) 106 82
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t129 : ((10299099093/200000000000 : ℚ) : ℝ) ≤ stT106 129 := by
  have hc : ((584877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10299099093/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((584877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c130 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-192537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2205679/5000000) (δ := 563/100000000) (ψ := -1027087/1000000) 106 82
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t130 : ((-168910161633/10000000000000 : ℚ) : ℝ) ≤ stT106 130 := by
  have hc : ((-192587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168910161633/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-192587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c131 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-26397/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 322101/500000) (δ := 823/100000000) (ψ := -1027087/1000000) 106 82
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t131 : ((-73806579357/1000000000000 : ℚ) : ℝ) ≤ stT106 131 := by
  have hc : ((-422377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73806579357/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-422377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c132 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-242757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290029/400000) (δ := 213/25000000) (ψ := -1027087/1000000) 106 83
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t132 : ((-422607804671/5000000000000 : ℚ) : ℝ) ≤ stT106 132 := by
  have hc : ((-485539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422607804671/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-485539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c133 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-505093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1050143/2000000) (δ := 193/25000000) (ψ := -1027087/1000000) 106 83
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t133 : ((-43801454673/1000000000000 : ℚ) : ℝ) ≤ stT106 133 := by
  have hc : ((-505143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43801454673/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-505143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c134 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((261447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3265687/10000000) (δ := 67/6250000) (ψ := -1027087/1000000) 106 83
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t134 : ((56453125899/2500000000000 : ℚ) : ℝ) ≤ stT106 134 := by
  have hc : ((261397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56453125899/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((261397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c135 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((108591/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -647709/5000000) (δ := 811/100000000) (ψ := -1027087/1000000) 106 83
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t135 : ((186909536209/2500000000000 : ℚ) : ℝ) ≤ stT106 135 := by
  have hc : ((434339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186909536209/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((434339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c136 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((482661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66031/1000000) (δ := 871/100000000) (ψ := -1027087/1000000) 106 83
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t136 : ((25866031807/312500000000 : ℚ) : ℝ) ≤ stT106 136 := by
  have hc : ((120659/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25866031807/312500000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((120659/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c137 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((50563/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2601711/10000000) (δ := 203/25000000) (ψ := -1027087/1000000) 106 83
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t137 : ((21597290603/500000000000 : ℚ) : ℝ) ≤ stT106 137 := by
  have hc : ((25279/50000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21597290603/500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((25279/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c138 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-2981/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141531/312500) (δ := 871/100000000) (ψ := -1027087/1000000) 106 83
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t138 : ((-20305033221/1000000000000 : ℚ) : ℝ) ≤ stT106 138 := by
  have hc : ((-23853/100000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20305033221/1000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-23853/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c139 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-105597/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3221179/5000000) (δ := 183/25000000) (ψ := -1027087/1000000) 106 83
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t139 : ((-358286060057/5000000000000 : ℚ) : ℝ) ≤ stT106 139 := by
  have hc : ((-422413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358286060057/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-422413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c140 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-981007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1841489/2500000) (δ := 861/100000000) (ψ := -1027087/1000000) 106 84
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t140 : ((-165829045767/2000000000000 : ℚ) : ℝ) ≤ stT106 140 := by
  have hc : ((-981057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165829045767/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-981057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c141 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-290979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5479827/10000000) (δ := 461/50000000) (ψ := -1027087/1000000) 106 84
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t141 : ((-7658425019/156250000000 : ℚ) : ℝ) ≤ stT106 141 := by
  have hc : ((-72751/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7658425019/156250000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-72751/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c142 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((31909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3607027/10000000) (δ := 301/50000000) (ψ := -1027087/1000000) 106 84
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t142 : ((53533873533/5000000000000 : ℚ) : ℝ) ≤ stT106 142 := by
  have hc : ((63793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53533873533/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((63793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c143 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((765519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174737/1000000) (δ := 741/100000000) (ψ := -1027087/1000000) 106 84
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t143 : ((320058663749/5000000000000 : ℚ) : ℝ) ≤ stT106 143 := by
  have hc : ((765469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320058663749/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((765469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c144 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((999211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99327/10000000) (δ := 521/50000000) (ψ := -1027087/1000000) 106 84
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t144 : ((832633833613/10000000000000 : ℚ) : ℝ) ≤ stT106 144 := by
  have hc : ((999161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((832633833613/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((999161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c145 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((715611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 483311/2500000) (δ := 641/100000000) (ψ := -1027087/1000000) 106 84
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t145 : ((297120247347/5000000000000 : ℚ) : ℝ) ≤ stT106 145 := by
  have hc : ((715561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297120247347/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((715561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c146 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((68919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3754557/10000000) (δ := 861/100000000) (ψ := -1027087/1000000) 106 84
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t146 : ((11399265749/2000000000000 : ℚ) : ℝ) ≤ stT106 146 := by
  have hc : ((68869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11399265749/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((68869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c147 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-24353/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2781719/5000000) (δ := 451/50000000) (ψ := -1027087/1000000) 106 84
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t147 : ((-4017537477/80000000000 : ℚ) : ℝ) ≤ stT106 147 := by
  have hc : ((-4871/8000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4017537477/80000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-4871/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c148 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-490273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1472011/2000000) (δ := 381/50000000) (ψ := -1027087/1000000) 106 84
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t148 : ((-40302250451/500000000000 : ℚ) : ℝ) ≤ stT106 148 := by
  have hc : ((-245149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40302250451/500000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-245149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c149 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-869683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656339/1000000) (δ := 103/10000000) (ψ := -1027087/1000000) 106 85
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t149 : ((-22266034533/312500000000 : ℚ) : ℝ) ≤ stT106 149 := by
  have hc : ((-869733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22266034533/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-869733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c150 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-84673/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -598851/1250000) (δ := 973/100000000) (ψ := -1027087/1000000) 106 85
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t150 : ((-138290913387/5000000000000 : ℚ) : ℝ) ≤ stT106 150 := by
  have hc : ((-169371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138290913387/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-169371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c151 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((175573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -757501/2500000) (δ := 69/10000000) (ψ := -1027087/1000000) 106 85
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t151 : ((8928678489/312500000000 : ℚ) : ℝ) ≤ stT106 151 := by
  have hc : ((43887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8928678489/312500000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((43887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c152 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((174321/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1280823/10000000) (δ := 87/10000000) (ψ := -1027087/1000000) 106 85
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t152 : ((141384872277/2000000000000 : ℚ) : ℝ) ≤ stT106 152 := by
  have hc : ((174311/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141384872277/2000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((174311/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c153 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((983347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57111/1250000) (δ := 87/10000000) (ψ := -1027087/1000000) 106 85
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t153 : ((198737106561/2500000000000 : ℚ) : ℝ) ≤ stT106 153 := by
  have hc : ((983297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198737106561/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((983297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c154 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((160573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2183279/10000000) (δ := 21/2000000) (ψ := -1027087/1000000) 106 85
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t154 : ((129383183231/2500000000000 : ℚ) : ℝ) ≤ stT106 154 := by
  have hc : ((321121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129383183231/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((321121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c155 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((5699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 779699/2000000) (δ := 91/10000000) (ψ := -1027087/1000000) 106 85
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t155 : ((2278732303/2500000000000 : ℚ) : ℝ) ≤ stT106 155 := by
  have hc : ((2837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2278732303/2500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((2837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c156 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-310601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5602681/10000000) (δ := 101/10000000) (ψ := -1027087/1000000) 106 85
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t156 : ((-124349955633/2500000000000 : ℚ) : ℝ) ≤ stT106 156 := by
  have hc : ((-155313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124349955633/2500000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-155313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c157 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-487597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3647989/5000000) (δ := 101/10000000) (ψ := -1027087/1000000) 106 85
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t157 : ((-194582389557/2500000000000 : ℚ) : ℝ) ≤ stT106 157 := by
  have hc : ((-243811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194582389557/2500000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-243811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c158 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-900527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42059/62500) (δ := 9/1250000) (ψ := -1027087/1000000) 106 86
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t158 : ((-358230618483/5000000000000 : ℚ) : ℝ) ≤ stT106 158 := by
  have hc : ((-900577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358230618483/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-900577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c159 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-54619/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -505751/1000000) (δ := 13/1250000) (ψ := -1027087/1000000) 106 86
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t159 : ((-43320663763/1250000000000 : ℚ) : ℝ) ≤ stT106 159 := by
  have hc : ((-218501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43320663763/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-218501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c160 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((105389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3396063/10000000) (δ := 23/2500000) (ψ := -1027087/1000000) 106 86
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t160 : ((20824378029/1250000000000 : ℚ) : ℝ) ≤ stT106 160 := by
  have hc : ((26341/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20824378029/1250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((26341/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c161 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((383069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1744967/10000000) (δ := 683/100000000) (ψ := -1027087/1000000) 106 86
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t161 : ((7547020171/125000000000 : ℚ) : ℝ) ≤ stT106 161 := by
  have hc : ((95761/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7547020171/125000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((95761/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c162 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((999133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20819/2000000) (δ := 7/1000000) (ψ := -1027087/1000000) 106 86
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t162 : ((392476768471/5000000000000 : ℚ) : ℝ) ≤ stT106 162 := by
  have hc : ((999083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392476768471/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((999083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c163 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((819263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1526679/10000000) (δ := 27/2500000) (ψ := -1027087/1000000) 106 86
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t163 : ((32082838719/500000000000 : ℚ) : ℝ) ≤ stT106 163 := by
  have hc : ((819213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32082838719/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((819213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c164 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((306777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3147479/10000000) (δ := 1/125000) (ψ := -1027087/1000000) 106 86
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t164 : ((59878324759/2500000000000 : ℚ) : ℝ) ≤ stT106 164 := by
  have hc : ((306727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59878324759/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((306727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c165 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-163239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4758427/10000000) (δ := 783/100000000) (ψ := -1027087/1000000) 106 86
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t165 : ((-1985950949/78125000000 : ℚ) : ℝ) ≤ stT106 165 := by
  have hc : ((-5102/15625 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1985950949/78125000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-5102/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c166 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-826611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158991/250000) (δ := 923/100000000) (ψ := -1027087/1000000) 106 86
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t166 : ((-641613761811/10000000000000 : ℚ) : ℝ) ≤ stT106 166 := by
  have hc : ((-826661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-641613761811/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-826661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c167 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-999243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7756727/10000000) (δ := 949/100000000) (ψ := -1027087/1000000) 106 87
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t167 : ((-12082451663/156250000000 : ℚ) : ℝ) ≤ stT106 167 := by
  have hc : ((-999293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12082451663/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-999293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c168 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-39137/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6174633/10000000) (δ := 407/50000000) (ψ := -1027087/1000000) 106 87
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t168 : ((-60393579243/1000000000000 : ℚ) : ℝ) ≤ stT106 168 := by
  have hc : ((-78279/100000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60393579243/1000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-78279/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c169 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-266707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -575241/1250000) (δ := 929/100000000) (ψ := -1027087/1000000) 106 87
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t169 : ((-205197753867/10000000000000 : ℚ) : ℝ) ≤ stT106 169 := by
  have hc : ((-266757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205197753867/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-266757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c170 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((173981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3038501/10000000) (δ := 669/100000000) (ψ := -1027087/1000000) 106 87
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t170 : ((8338624349/312500000000 : ℚ) : ℝ) ≤ stT106 170 := by
  have hc : ((43489/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8338624349/312500000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((43489/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c171 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((414439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -296849/2000000) (δ := 287/50000000) (ψ := -1027087/1000000) 106 87
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t171 : ((158455129833/2500000000000 : ℚ) : ℝ) ≤ stT106 171 := by
  have hc : ((207207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158455129833/2500000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((207207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c172 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((999703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60949/10000000) (δ := 397/50000000) (ψ := -1027087/1000000) 106 87
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t172 : ((190556853819/2500000000000 : ℚ) : ℝ) ≤ stT106 172 := by
  have hc : ((999653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190556853819/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((999653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c173 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((50173/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 319437/2000000) (δ := 487/50000000) (ψ := -1027087/1000000) 106 87
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t173 : ((61029445463/1000000000000 : ℚ) : ℝ) ≤ stT106 173 := by
  have hc : ((401359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61029445463/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((401359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c174 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((315487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3124567/10000000) (δ := 517/50000000) (ψ := -1027087/1000000) 106 87
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t174 : ((119566079413/5000000000000 : ℚ) : ℝ) ≤ stT106 174 := by
  have hc : ((315437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119566079413/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((315437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c175 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-282579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1160799/2500000) (δ := 387/50000000) (ψ := -1027087/1000000) 106 87
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t175 : ((-213647457341/10000000000000 : ℚ) : ℝ) ≤ stT106 175 := by
  have hc : ((-282629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213647457341/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-282629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c176 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-777369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6153171/10000000) (δ := 487/50000000) (ψ := -1027087/1000000) 106 87
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t176 : ((-586002116401/10000000000000 : ℚ) : ℝ) ≤ stT106 176 := by
  have hc : ((-777419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-586002116401/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-777419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c177 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-996821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119603/156250) (δ := 729/100000000) (ψ := -1027087/1000000) 106 87
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t177 : ((-749295096537/10000000000000 : ℚ) : ℝ) ≤ stT106 177 := by
  have hc : ((-996871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-749295096537/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-996871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c178 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-434547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656041/1000000) (δ := 279/50000000) (ψ := -1027087/1000000) 106 88
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t178 : ((-20357851269/312500000000 : ℚ) : ℝ) ≤ stT106 178 := by
  have hc : ((-108643/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20357851269/312500000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-108643/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c179 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-221763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1268953/2500000) (δ := 509/50000000) (ψ := -1027087/1000000) 106 88
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t179 : ((-10360770973/312500000000 : ℚ) : ℝ) ≤ stT106 179 := by
  have hc : ((-55447/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10360770973/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-55447/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c180 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((32657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -719897/2000000) (δ := 269/50000000) (ψ := -1027087/1000000) 106 88
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t180 : ((9732696519/1000000000000 : ℚ) : ℝ) ≤ stT106 180 := by
  have hc : ((65289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9732696519/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((65289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c181 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((658077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2131337/10000000) (δ := 369/50000000) (ψ := -1027087/1000000) 106 88
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t181 : ((244553760469/5000000000000 : ℚ) : ℝ) ≤ stT106 181 := by
  have hc : ((658027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244553760469/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((658027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c182 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((964167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671279/10000000) (δ := 177/20000000) (ψ := -1027087/1000000) 106 88
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t182 : ((714650762133/10000000000000 : ℚ) : ℝ) ≤ stT106 182 := by
  have hc : ((964117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((714650762133/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((964117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c183 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((475813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39039/500000) (δ := 109/20000000) (ψ := -1027087/1000000) 106 88
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t183 : ((87928120287/1250000000000 : ℚ) : ℝ) ≤ stT106 183 := by
  have hc : ((118947/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87928120287/1250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((118947/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c184 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((125887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88997/400000) (δ := 117/20000000) (ψ := -1027087/1000000) 106 88
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t184 : ((92797657293/2000000000000 : ℚ) : ℝ) ≤ stT106 184 := by
  have hc : ((125877/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92797657293/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((125877/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c185 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((106099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3661243/10000000) (δ := 409/50000000) (ψ := -1027087/1000000) 106 88
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t185 : ((38984354743/5000000000000 : ℚ) : ℝ) ≤ stT106 185 := by
  have hc : ((106049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38984354743/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((106049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c186 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-22427/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2544909/5000000) (δ := 153/20000000) (ψ := -1027087/1000000) 106 88
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t186 : ((-8223058431/250000000000 : ℚ) : ℝ) ≤ stT106 186 := by
  have hc : ((-44859/100000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8223058431/250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-44859/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c187 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-429547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6510733/10000000) (δ := 449/50000000) (ψ := -1027087/1000000) 106 88
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t187 : ((-78533601289/1250000000000 : ℚ) : ℝ) ≤ stT106 187 := by
  have hc : ((-107393/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78533601289/1250000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-107393/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c188 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-999607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3891947/5000000) (δ := 127/20000000) (ψ := -1027087/1000000) 106 89
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t188 : ((-29162993661/400000000000 : ℚ) : ℝ) ≤ stT106 188 := by
  have hc : ((-999657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29162993661/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-999657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c189 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-415367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1275611/2000000) (δ := 29/3125000) (ψ := -1027087/1000000) 106 89
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t189 : ((-9442288533/156250000000 : ℚ) : ℝ) ≤ stT106 189 := by
  have hc : ((-12981/15625 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9442288533/156250000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-12981/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c190 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-204363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -995927/2000000) (δ := 147/20000000) (ψ := -1027087/1000000) 106 89
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t190 : ((-37069698269/1250000000000 : ℚ) : ℝ) ≤ stT106 190 := by
  have hc : ((-51097/125000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37069698269/1250000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-51097/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c191 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((134961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -717711/2000000) (δ := 3/390625) (ψ := -1027087/1000000) 106 89
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t191 : ((48809045957/5000000000000 : ℚ) : ℝ) ≤ stT106 191 := by
  have hc : ((134911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48809045957/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((134911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c192 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((635689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110237/500000) (δ := 151/20000000) (ψ := -1027087/1000000) 106 89
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t192 : ((458732402993/10000000000000 : ℚ) : ℝ) ≤ stT106 192 := by
  have hc : ((635639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458732402993/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((635639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c193 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((472819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414057/5000000) (δ := 183/20000000) (ψ := -1027087/1000000) 106 89
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t193 : ((34032421311/500000000000 : ℚ) : ℝ) ≤ stT106 193 := by
  have hc : ((236397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34032421311/500000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((236397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c194 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((976643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270699/5000000) (δ := 119/20000000) (ψ := -1027087/1000000) 106 89
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t194 : ((350576378547/5000000000000 : ℚ) : ℝ) ≤ stT106 194 := by
  have hc : ((976593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((350576378547/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((976593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c195 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((723769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1903869/10000000) (δ := 119/20000000) (ψ := -1027087/1000000) 106 89
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t195 : ((259132653983/5000000000000 : ℚ) : ℝ) ≤ stT106 195 := by
  have hc : ((723719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259132653983/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((723719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c196 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((52777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3259371/10000000) (δ := 123/20000000) (ψ := -1027087/1000000) 106 89
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t196 : ((7538135319/400000000000 : ℚ) : ℝ) ≤ stT106 196 := by
  have hc : ((52767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7538135319/400000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((52767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c197 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-269037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2303987/5000000) (δ := 197/25000000) (ψ := -1027087/1000000) 106 89
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t197 : ((-191716683977/10000000000000 : ℚ) : ℝ) ≤ stT106 197 := by
  have hc : ((-269087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191716683977/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-269087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c198 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-723669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5949749/10000000) (δ := 3/390625) (ψ := -1027087/1000000) 106 89
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t198 : ((-51432538173/1000000000000 : ℚ) : ℝ) ≤ stT106 198 := by
  have hc : ((-723719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51432538173/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-723719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c199 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-974191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1456953/2000000) (δ := 101/12500000) (ψ := -1027087/1000000) 106 89
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t199 : ((-345310954281/5000000000000 : ℚ) : ℝ) ≤ stT106 199 := by
  have hc : ((-974241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345310954281/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-974241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_c200 :
    |Real.cos (((106 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-477127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56759/80000) (δ := 343/50000000) (ψ := -1027087/1000000) 106 90
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st106_t200 : ((-10543672477/156250000000 : ℚ) : ℝ) ≤ stT106 200 := by
  have hc : ((-14911/15625 : ℚ) : ℝ)
      ≤ Real.cos (((106 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st106_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10543672477/156250000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-14911/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st106_p1 : ((32329/62500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT106 (i+1) := by
  rw [Finset.sum_range_one]
  exact st106_t1

theorem st106_p2 : ((9581372492763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT106 (i+1))
      = (∑ i ∈ Finset.range 1, stT106 (i+1)) + stT106 2 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 1
    simpa using h
  have hprev := st106_p1
  have hstep := st106_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p3 : ((3855831980367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT106 (i+1))
      = (∑ i ∈ Finset.range 2, stT106 (i+1)) + stT106 3 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 2
    simpa using h
  have hprev := st106_p2
  have hstep := st106_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p4 : ((2964348011271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT106 (i+1))
      = (∑ i ∈ Finset.range 3, stT106 (i+1)) + stT106 4 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 3
    simpa using h
  have hprev := st106_p3
  have hstep := st106_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p5 : ((1178592801519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT106 (i+1))
      = (∑ i ∈ Finset.range 4, stT106 (i+1)) + stT106 5 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 4
    simpa using h
  have hprev := st106_p4
  have hstep := st106_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p6 : ((-397374940411/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT106 (i+1))
      = (∑ i ∈ Finset.range 5, stT106 (i+1)) + stT106 6 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 5
    simpa using h
  have hprev := st106_p5
  have hstep := st106_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p7 : ((1787557168869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT106 (i+1))
      = (∑ i ∈ Finset.range 6, stT106 (i+1)) + stT106 7 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 6
    simpa using h
  have hprev := st106_p6
  have hstep := st106_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p8 : ((238618711803/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT106 (i+1))
      = (∑ i ∈ Finset.range 7, stT106 (i+1)) + stT106 8 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 7
    simpa using h
  have hprev := st106_p7
  have hstep := st106_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p9 : ((114689482797/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT106 (i+1))
      = (∑ i ∈ Finset.range 8, stT106 (i+1)) + stT106 9 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 8
    simpa using h
  have hprev := st106_p8
  have hstep := st106_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p10 : ((5450795140181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT106 (i+1))
      = (∑ i ∈ Finset.range 9, stT106 (i+1)) + stT106 10 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 9
    simpa using h
  have hprev := st106_p9
  have hstep := st106_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p11 : ((642780030853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT106 (i+1))
      = (∑ i ∈ Finset.range 10, stT106 (i+1)) + stT106 11 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 10
    simpa using h
  have hprev := st106_p10
  have hstep := st106_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p12 : ((1424869120261/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT106 (i+1))
      = (∑ i ∈ Finset.range 11, stT106 (i+1)) + stT106 12 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 11
    simpa using h
  have hprev := st106_p11
  have hstep := st106_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p13 : ((3152223825119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT106 (i+1))
      = (∑ i ∈ Finset.range 12, stT106 (i+1)) + stT106 13 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 12
    simpa using h
  have hprev := st106_p12
  have hstep := st106_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p14 : ((1049049911749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT106 (i+1))
      = (∑ i ∈ Finset.range 13, stT106 (i+1)) + stT106 14 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 13
    simpa using h
  have hprev := st106_p13
  have hstep := st106_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p15 : ((1804007711021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT106 (i+1))
      = (∑ i ∈ Finset.range 14, stT106 (i+1)) + stT106 15 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 14
    simpa using h
  have hprev := st106_p14
  have hstep := st106_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p16 : ((2960926461021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT106 (i+1))
      = (∑ i ∈ Finset.range 15, stT106 (i+1)) + stT106 16 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 15
    simpa using h
  have hprev := st106_p15
  have hstep := st106_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p17 : ((4137272628141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT106 (i+1))
      = (∑ i ∈ Finset.range 16, stT106 (i+1)) + stT106 17 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 16
    simpa using h
  have hprev := st106_p16
  have hstep := st106_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p18 : ((1297039194849/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT106 (i+1))
      = (∑ i ∈ Finset.range 17, stT106 (i+1)) + stT106 18 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 17
    simpa using h
  have hprev := st106_p17
  have hstep := st106_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p19 : ((361676925843/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT106 (i+1))
      = (∑ i ∈ Finset.range 18, stT106 (i+1)) + stT106 19 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 18
    simpa using h
  have hprev := st106_p18
  have hstep := st106_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p20 : ((136490898183/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT106 (i+1))
      = (∑ i ∈ Finset.range 19, stT106 (i+1)) + stT106 20 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 19
    simpa using h
  have hprev := st106_p19
  have hstep := st106_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p21 : ((8765703403509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT106 (i+1))
      = (∑ i ∈ Finset.range 20, stT106 (i+1)) + stT106 21 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 20
    simpa using h
  have hprev := st106_p20
  have hstep := st106_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p22 : ((7972506883173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT106 (i+1))
      = (∑ i ∈ Finset.range 21, stT106 (i+1)) + stT106 22 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 21
    simpa using h
  have hprev := st106_p21
  have hstep := st106_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p23 : ((9908296188741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT106 (i+1))
      = (∑ i ∈ Finset.range 22, stT106 (i+1)) + stT106 23 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 22
    simpa using h
  have hprev := st106_p22
  have hstep := st106_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p24 : ((1027279855287/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT106 (i+1))
      = (∑ i ∈ Finset.range 23, stT106 (i+1)) + stT106 24 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 23
    simpa using h
  have hprev := st106_p23
  have hstep := st106_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p25 : ((8314851573897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT106 (i+1))
      = (∑ i ∈ Finset.range 24, stT106 (i+1)) + stT106 25 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 24
    simpa using h
  have hprev := st106_p24
  have hstep := st106_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p26 : ((9666789676213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT106 (i+1))
      = (∑ i ∈ Finset.range 25, stT106 (i+1)) + stT106 26 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 25
    simpa using h
  have hprev := st106_p25
  have hstep := st106_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p27 : ((9855402223213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT106 (i+1))
      = (∑ i ∈ Finset.range 26, stT106 (i+1)) + stT106 27 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 26
    simpa using h
  have hprev := st106_p26
  have hstep := st106_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p28 : ((4242231127427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT106 (i+1))
      = (∑ i ∈ Finset.range 27, stT106 (i+1)) + stT106 28 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 27
    simpa using h
  have hprev := st106_p27
  have hstep := st106_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p29 : ((10310948226983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT106 (i+1))
      = (∑ i ∈ Finset.range 28, stT106 (i+1)) + stT106 29 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 28
    simpa using h
  have hprev := st106_p28
  have hstep := st106_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p30 : ((8551676015977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT106 (i+1))
      = (∑ i ∈ Finset.range 29, stT106 (i+1)) + stT106 30 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 29
    simpa using h
  have hprev := st106_p29
  have hstep := st106_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p31 : ((10028861358463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT106 (i+1))
      = (∑ i ∈ Finset.range 30, stT106 (i+1)) + stT106 31 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 30
    simpa using h
  have hprev := st106_p30
  have hstep := st106_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p32 : ((8834123102581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT106 (i+1))
      = (∑ i ∈ Finset.range 31, stT106 (i+1)) + stT106 32 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 31
    simpa using h
  have hprev := st106_p31
  have hstep := st106_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p33 : ((9848095529389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT106 (i+1))
      = (∑ i ∈ Finset.range 32, stT106 (i+1)) + stT106 33 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 32
    simpa using h
  have hprev := st106_p32
  have hstep := st106_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p34 : ((8881044078751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT106 (i+1))
      = (∑ i ∈ Finset.range 33, stT106 (i+1)) + stT106 34 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 33
    simpa using h
  have hprev := st106_p33
  have hstep := st106_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p35 : ((9927877177771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT106 (i+1))
      = (∑ i ∈ Finset.range 34, stT106 (i+1)) + stT106 35 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 34
    simpa using h
  have hprev := st106_p34
  have hstep := st106_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p36 : ((8705343599931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT106 (i+1))
      = (∑ i ∈ Finset.range 35, stT106 (i+1)) + stT106 36 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 35
    simpa using h
  have hprev := st106_p35
  have hstep := st106_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p37 : ((10139977176737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT106 (i+1))
      = (∑ i ∈ Finset.range 36, stT106 (i+1)) + stT106 37 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 36
    simpa using h
  have hprev := st106_p36
  have hstep := st106_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p38 : ((2137131871053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT106 (i+1))
      = (∑ i ∈ Finset.range 37, stT106 (i+1)) + stT106 38 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 37
    simpa using h
  have hprev := st106_p37
  have hstep := st106_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p39 : ((10120039069141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT106 (i+1))
      = (∑ i ∈ Finset.range 38, stT106 (i+1)) + stT106 39 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 38
    simpa using h
  have hprev := st106_p38
  have hstep := st106_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p40 : ((8861980525567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT106 (i+1))
      = (∑ i ∈ Finset.range 39, stT106 (i+1)) + stT106 40 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 39
    simpa using h
  have hprev := st106_p39
  have hstep := st106_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p41 : ((2366023542571/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT106 (i+1))
      = (∑ i ∈ Finset.range 40, stT106 (i+1)) + stT106 41 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 40
    simpa using h
  have hprev := st106_p40
  have hstep := st106_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p42 : ((1219695066311/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT106 (i+1))
      = (∑ i ∈ Finset.range 41, stT106 (i+1)) + stT106 42 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 41
    simpa using h
  have hprev := st106_p41
  have hstep := st106_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p43 : ((53894826529/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT106 (i+1))
      = (∑ i ∈ Finset.range 42, stT106 (i+1)) + stT106 43 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 42
    simpa using h
  have hprev := st106_p42
  have hstep := st106_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p44 : ((2532522637113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT106 (i+1))
      = (∑ i ∈ Finset.range 43, stT106 (i+1)) + stT106 44 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 43
    simpa using h
  have hprev := st106_p43
  have hstep := st106_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p45 : ((2255326604103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT106 (i+1))
      = (∑ i ∈ Finset.range 44, stT106 (i+1)) + stT106 45 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 44
    simpa using h
  have hprev := st106_p44
  have hstep := st106_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p46 : ((9060781036299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT106 (i+1))
      = (∑ i ∈ Finset.range 45, stT106 (i+1)) + stT106 46 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 45
    simpa using h
  have hprev := st106_p45
  have hstep := st106_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p47 : ((1014210525433/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT106 (i+1))
      = (∑ i ∈ Finset.range 46, stT106 (i+1)) + stT106 47 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 46
    simpa using h
  have hprev := st106_p46
  have hstep := st106_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p48 : ((4360256342461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT106 (i+1))
      = (∑ i ∈ Finset.range 47, stT106 (i+1)) + stT106 48 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 47
    simpa using h
  have hprev := st106_p47
  have hstep := st106_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p49 : ((4664853393939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT106 (i+1))
      = (∑ i ∈ Finset.range 48, stT106 (i+1)) + stT106 49 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 48
    simpa using h
  have hprev := st106_p48
  have hstep := st106_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p50 : ((10080248011747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT106 (i+1))
      = (∑ i ∈ Finset.range 49, stT106 (i+1)) + stT106 50 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 49
    simpa using h
  have hprev := st106_p49
  have hstep := st106_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p51 : ((542536183409/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT106 (i+1))
      = (∑ i ∈ Finset.range 50, stT106 (i+1)) + stT106 51 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 50
    simpa using h
  have hprev := st106_p50
  have hstep := st106_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p52 : ((4645777318147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT106 (i+1))
      = (∑ i ∈ Finset.range 51, stT106 (i+1)) + stT106 52 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 51
    simpa using h
  have hprev := st106_p51
  have hstep := st106_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p53 : ((10140358736389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT106 (i+1))
      = (∑ i ∈ Finset.range 52, stT106 (i+1)) + stT106 53 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 52
    simpa using h
  have hprev := st106_p52
  have hstep := st106_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p54 : ((8823677357537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT106 (i+1))
      = (∑ i ∈ Finset.range 53, stT106 (i+1)) + stT106 54 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 53
    simpa using h
  have hprev := st106_p53
  have hstep := st106_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p55 : ((1796631040813/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT106 (i+1))
      = (∑ i ∈ Finset.range 54, stT106 (i+1)) + stT106 55 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 54
    simpa using h
  have hprev := st106_p54
  have hstep := st106_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p56 : ((10181810995617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT106 (i+1))
      = (∑ i ∈ Finset.range 55, stT106 (i+1)) + stT106 56 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 55
    simpa using h
  have hprev := st106_p55
  have hstep := st106_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p57 : ((2316562519107/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT106 (i+1))
      = (∑ i ∈ Finset.range 56, stT106 (i+1)) + stT106 57 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 56
    simpa using h
  have hprev := st106_p56
  have hstep := st106_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p58 : ((8596793077633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT106 (i+1))
      = (∑ i ∈ Finset.range 57, stT106 (i+1)) + stT106 58 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 57
    simpa using h
  have hprev := st106_p57
  have hstep := st106_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p59 : ((9842857077313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT106 (i+1))
      = (∑ i ∈ Finset.range 58, stT106 (i+1)) + stT106 59 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 58
    simpa using h
  have hprev := st106_p58
  have hstep := st106_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p60 : ((9949786237351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT106 (i+1))
      = (∑ i ∈ Finset.range 59, stT106 (i+1)) + stT106 60 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 59
    simpa using h
  have hprev := st106_p59
  have hstep := st106_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p61 : ((433776934077/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT106 (i+1))
      = (∑ i ∈ Finset.range 60, stT106 (i+1)) + stT106 61 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 60
    simpa using h
  have hprev := st106_p60
  have hstep := st106_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p62 : ((4495550455007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT106 (i+1))
      = (∑ i ∈ Finset.range 61, stT106 (i+1)) + stT106 62 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 61
    simpa using h
  have hprev := st106_p61
  have hstep := st106_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p63 : ((10162720946559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT106 (i+1))
      = (∑ i ∈ Finset.range 62, stT106 (i+1)) + stT106 63 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 62
    simpa using h
  have hprev := st106_p62
  have hstep := st106_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p64 : ((9591067989237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT106 (i+1))
      = (∑ i ∈ Finset.range 63, stT106 (i+1)) + stT106 64 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 63
    simpa using h
  have hprev := st106_p63
  have hstep := st106_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p65 : ((8532008012569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT106 (i+1))
      = (∑ i ∈ Finset.range 64, stT106 (i+1)) + stT106 65 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 64
    simpa using h
  have hprev := st106_p64
  have hstep := st106_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p66 : ((9222016549893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT106 (i+1))
      = (∑ i ∈ Finset.range 65, stT106 (i+1)) + stT106 66 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 65
    simpa using h
  have hprev := st106_p65
  have hstep := st106_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p67 : ((10217436939071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT106 (i+1))
      = (∑ i ∈ Finset.range 66, stT106 (i+1)) + stT106 67 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 66
    simpa using h
  have hprev := st106_p66
  have hstep := st106_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p68 : ((9514791323607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT106 (i+1))
      = (∑ i ∈ Finset.range 67, stT106 (i+1)) + stT106 68 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 67
    simpa using h
  have hprev := st106_p67
  have hstep := st106_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p69 : ((1703500979427/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT106 (i+1))
      = (∑ i ∈ Finset.range 68, stT106 (i+1)) + stT106 69 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 68
    simpa using h
  have hprev := st106_p68
  have hstep := st106_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p70 : ((9141193991183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT106 (i+1))
      = (∑ i ∈ Finset.range 69, stT106 (i+1)) + stT106 70 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 69
    simpa using h
  have hprev := st106_p69
  have hstep := st106_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p71 : ((40771235771/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT106 (i+1))
      = (∑ i ∈ Finset.range 70, stT106 (i+1)) + stT106 71 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 70
    simpa using h
  have hprev := st106_p70
  have hstep := st106_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p72 : ((4870409474719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT106 (i+1))
      = (∑ i ∈ Finset.range 71, stT106 (i+1)) + stT106 72 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 71
    simpa using h
  have hprev := st106_p71
  have hstep := st106_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p73 : ((4308756260601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT106 (i+1))
      = (∑ i ∈ Finset.range 72, stT106 (i+1)) + stT106 73 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 72
    simpa using h
  have hprev := st106_p72
  have hstep := st106_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p74 : ((4399179456261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT106 (i+1))
      = (∑ i ∈ Finset.range 73, stT106 (i+1)) + stT106 74 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 73
    simpa using h
  have hprev := st106_p73
  have hstep := st106_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p75 : ((4976480958861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT106 (i+1))
      = (∑ i ∈ Finset.range 74, stT106 (i+1)) + stT106 75 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 74
    simpa using h
  have hprev := st106_p74
  have hstep := st106_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p76 : ((5066979677671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT106 (i+1))
      = (∑ i ∈ Finset.range 75, stT106 (i+1)) + stT106 76 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 75
    simpa using h
  have hprev := st106_p75
  have hstep := st106_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p77 : ((4530465708537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT106 (i+1))
      = (∑ i ∈ Finset.range 76, stT106 (i+1)) + stT106 77 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 76
    simpa using h
  have hprev := st106_p76
  have hstep := st106_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p78 : ((4236120984213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT106 (i+1))
      = (∑ i ∈ Finset.range 77, stT106 (i+1)) + stT106 78 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 77
    simpa using h
  have hprev := st106_p77
  have hstep := st106_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p79 : ((9282123469419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT106 (i+1))
      = (∑ i ∈ Finset.range 78, stT106 (i+1)) + stT106 79 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 78
    simpa using h
  have hprev := st106_p78
  have hstep := st106_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p80 : ((511281408201/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT106 (i+1))
      = (∑ i ∈ Finset.range 79, stT106 (i+1)) + stT106 80 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 79
    simpa using h
  have hprev := st106_p79
  have hstep := st106_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p81 : ((2471075861629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT106 (i+1))
      = (∑ i ∈ Finset.range 80, stT106 (i+1)) + stT106 81 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 80
    simpa using h
  have hprev := st106_p80
  have hstep := st106_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p82 : ((548806708859/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT106 (i+1))
      = (∑ i ∈ Finset.range 81, stT106 (i+1)) + stT106 82 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 81
    simpa using h
  have hprev := st106_p81
  have hstep := st106_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p83 : ((8515772772737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT106 (i+1))
      = (∑ i ∈ Finset.range 82, stT106 (i+1)) + stT106 83 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 82
    simpa using h
  have hprev := st106_p82
  have hstep := st106_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p84 : ((9448608041999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT106 (i+1))
      = (∑ i ∈ Finset.range 83, stT106 (i+1)) + stT106 84 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 83
    simpa using h
  have hprev := st106_p83
  have hstep := st106_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p85 : ((10271662587987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT106 (i+1))
      = (∑ i ∈ Finset.range 84, stT106 (i+1)) + stT106 85 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 84
    simpa using h
  have hprev := st106_p84
  have hstep := st106_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p86 : ((394937269771/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT106 (i+1))
      = (∑ i ∈ Finset.range 85, stT106 (i+1)) + stT106 86 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 85
    simpa using h
  have hprev := st106_p85
  have hstep := st106_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p87 : ((1760368815929/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT106 (i+1))
      = (∑ i ∈ Finset.range 86, stT106 (i+1)) + stT106 87 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 86
    simpa using h
  have hprev := st106_p86
  have hstep := st106_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p88 : ((8459893448533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT106 (i+1))
      = (∑ i ∈ Finset.range 87, stT106 (i+1)) + stT106 88 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 87
    simpa using h
  have hprev := st106_p87
  have hstep := st106_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p89 : ((9270884433269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT106 (i+1))
      = (∑ i ∈ Finset.range 88, stT106 (i+1)) + stT106 89 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 88
    simpa using h
  have hprev := st106_p88
  have hstep := st106_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p90 : ((10203444896129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT106 (i+1))
      = (∑ i ∈ Finset.range 89, stT106 (i+1)) + stT106 90 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 89
    simpa using h
  have hprev := st106_p89
  have hstep := st106_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p91 : ((1264258383593/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT106 (i+1))
      = (∑ i ∈ Finset.range 90, stT106 (i+1)) + stT106 91 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 90
    simpa using h
  have hprev := st106_p90
  have hstep := st106_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p92 : ((2281671970841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT106 (i+1))
      = (∑ i ∈ Finset.range 91, stT106 (i+1)) + stT106 92 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 91
    simpa using h
  have hprev := st106_p91
  have hstep := st106_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p93 : ((2104603861987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT106 (i+1))
      = (∑ i ∈ Finset.range 92, stT106 (i+1)) + stT106 93 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 92
    simpa using h
  have hprev := st106_p92
  have hstep := st106_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p94 : ((8802721881127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT106 (i+1))
      = (∑ i ∈ Finset.range 93, stT106 (i+1)) + stT106 94 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 93
    simpa using h
  have hprev := st106_p93
  have hstep := st106_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p95 : ((393053235917/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT106 (i+1))
      = (∑ i ∈ Finset.range 94, stT106 (i+1)) + stT106 95 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 94
    simpa using h
  have hprev := st106_p94
  have hstep := st106_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p96 : ((2068107320893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT106 (i+1))
      = (∑ i ∈ Finset.range 95, stT106 (i+1)) + stT106 96 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 95
    simpa using h
  have hprev := st106_p95
  have hstep := st106_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p97 : ((2448060529259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT106 (i+1))
      = (∑ i ∈ Finset.range 96, stT106 (i+1)) + stT106 97 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 96
    simpa using h
  have hprev := st106_p96
  have hstep := st106_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p98 : ((70286718521/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT106 (i+1))
      = (∑ i ∈ Finset.range 97, stT106 (i+1)) + stT106 98 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 97
    simpa using h
  have hprev := st106_p97
  have hstep := st106_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p99 : ((8387139230449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT106 (i+1))
      = (∑ i ∈ Finset.range 98, stT106 (i+1)) + stT106 99 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 98
    simpa using h
  have hprev := st106_p98
  have hstep := st106_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p100 : ((1124775452423/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT106 (i+1))
      = (∑ i ∈ Finset.range 99, stT106 (i+1)) + stT106 100 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 99
    simpa using h
  have hprev := st106_p99
  have hstep := st106_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p101 : ((9983259403237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT106 (i+1))
      = (∑ i ∈ Finset.range 100, stT106 (i+1)) + stT106 101 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 100
    simpa using h
  have hprev := st106_p100
  have hstep := st106_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p102 : ((5177555049617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT106 (i+1))
      = (∑ i ∈ Finset.range 101, stT106 (i+1)) + stT106 102 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 101
    simpa using h
  have hprev := st106_p101
  have hstep := st106_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p103 : ((2439862877581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT106 (i+1))
      = (∑ i ∈ Finset.range 102, stT106 (i+1)) + stT106 103 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 102
    simpa using h
  have hprev := st106_p102
  have hstep := st106_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p104 : ((21959914023/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT106 (i+1))
      = (∑ i ∈ Finset.range 103, stT106 (i+1)) + stT106 104 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 103
    simpa using h
  have hprev := st106_p103
  have hstep := st106_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p105 : ((8355957876323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT106 (i+1))
      = (∑ i ∈ Finset.range 104, stT106 (i+1)) + stT106 105 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 104
    simpa using h
  have hprev := st106_p104
  have hstep := st106_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p106 : ((2216060014597/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT106 (i+1))
      = (∑ i ∈ Finset.range 105, stT106 (i+1)) + stT106 106 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 105
    simpa using h
  have hprev := st106_p105
  have hstep := st106_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p107 : ((2457658216777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT106 (i+1))
      = (∑ i ∈ Finset.range 106, stT106 (i+1)) + stT106 107 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 106
    simpa using h
  have hprev := st106_p106
  have hstep := st106_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p108 : ((5190691695179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT106 (i+1))
      = (∑ i ∈ Finset.range 107, stT106 (i+1)) + stT106 108 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 107
    simpa using h
  have hprev := st106_p107
  have hstep := st106_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p109 : ((2007435927493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT106 (i+1))
      = (∑ i ∈ Finset.range 108, stT106 (i+1)) + stT106 109 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 108
    simpa using h
  have hprev := st106_p108
  have hstep := st106_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p110 : ((9109925428409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT106 (i+1))
      = (∑ i ∈ Finset.range 109, stT106 (i+1)) + stT106 110 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 109
    simpa using h
  have hprev := st106_p109
  have hstep := st106_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p111 : ((8398839983759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT106 (i+1))
      = (∑ i ∈ Finset.range 110, stT106 (i+1)) + stT106 111 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 110
    simpa using h
  have hprev := st106_p110
  have hstep := st106_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p112 : ((8496829144281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT106 (i+1))
      = (∑ i ∈ Finset.range 111, stT106 (i+1)) + stT106 112 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 111
    simpa using h
  have hprev := st106_p111
  have hstep := st106_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p113 : ((9310984675481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT106 (i+1))
      = (∑ i ∈ Finset.range 112, stT106 (i+1)) + stT106 113 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 112
    simpa using h
  have hprev := st106_p112
  have hstep := st106_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p114 : ((1271270232727/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT106 (i+1))
      = (∑ i ∈ Finset.range 113, stT106 (i+1)) + stT106 114 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 113
    simpa using h
  have hprev := st106_p113
  have hstep := st106_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p115 : ((129848780979/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT106 (i+1))
      = (∑ i ∈ Finset.range 114, stT106 (i+1)) + stT106 115 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 114
    simpa using h
  have hprev := st106_p114
  have hstep := st106_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p116 : ((9802574793411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT106 (i+1))
      = (∑ i ∈ Finset.range 115, stT106 (i+1)) + stT106 116 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 115
    simpa using h
  have hprev := st106_p115
  have hstep := st106_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p117 : ((2219558433021/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT106 (i+1))
      = (∑ i ∈ Finset.range 116, stT106 (i+1)) + stT106 117 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 116
    simpa using h
  have hprev := st106_p116
  have hstep := st106_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p118 : ((8322860960909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT106 (i+1))
      = (∑ i ∈ Finset.range 117, stT106 (i+1)) + stT106 118 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 117
    simpa using h
  have hprev := st106_p117
  have hstep := st106_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p119 : ((8546912035787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT106 (i+1))
      = (∑ i ∈ Finset.range 118, stT106 (i+1)) + stT106 119 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 118
    simpa using h
  have hprev := st106_p118
  have hstep := st106_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p120 : ((9374027940857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT106 (i+1))
      = (∑ i ∈ Finset.range 119, stT106 (i+1)) + stT106 120 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 119
    simpa using h
  have hprev := st106_p119
  have hstep := st106_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p121 : ((10195366210427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT106 (i+1))
      = (∑ i ∈ Finset.range 120, stT106 (i+1)) + stT106 121 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 120
    simpa using h
  have hprev := st106_p120
  have hstep := st106_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p122 : ((10424120952903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT106 (i+1))
      = (∑ i ∈ Finset.range 121, stT106 (i+1)) + stT106 122 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 121
    simpa using h
  have hprev := st106_p121
  have hstep := st106_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p123 : ((9907669623663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT106 (i+1))
      = (∑ i ∈ Finset.range 122, stT106 (i+1)) + stT106 123 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 122
    simpa using h
  have hprev := st106_p122
  have hstep := st106_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p124 : ((1802865346499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT106 (i+1))
      = (∑ i ∈ Finset.range 123, stT106 (i+1)) + stT106 124 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 123
    simpa using h
  have hprev := st106_p123
  have hstep := st106_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p125 : ((8359071462979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT106 (i+1))
      = (∑ i ∈ Finset.range 124, stT106 (i+1)) + stT106 125 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 124
    simpa using h
  have hprev := st106_p124
  have hstep := st106_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p126 : ((8379132073639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT106 (i+1))
      = (∑ i ∈ Finset.range 125, stT106 (i+1)) + stT106 126 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 125
    simpa using h
  have hprev := st106_p125
  have hstep := st106_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p127 : ((362074566611/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT106 (i+1))
      = (∑ i ∈ Finset.range 126, stT106 (i+1)) + stT106 127 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 126
    simpa using h
  have hprev := st106_p126
  have hstep := st106_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p128 : ((9929229412033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT106 (i+1))
      = (∑ i ∈ Finset.range 127, stT106 (i+1)) + stT106 128 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 127
    simpa using h
  have hprev := st106_p127
  have hstep := st106_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p129 : ((10444184366683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT106 (i+1))
      = (∑ i ∈ Finset.range 128, stT106 (i+1)) + stT106 129 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 128
    simpa using h
  have hprev := st106_p128
  have hstep := st106_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p130 : ((205505484101/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT106 (i+1))
      = (∑ i ∈ Finset.range 129, stT106 (i+1)) + stT106 130 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 129
    simpa using h
  have hprev := st106_p129
  have hstep := st106_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p131 : ((238430210287/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT106 (i+1))
      = (∑ i ∈ Finset.range 130, stT106 (i+1)) + stT106 131 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 130
    simpa using h
  have hprev := st106_p130
  have hstep := st106_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p132 : ((4345996401069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT106 (i+1))
      = (∑ i ∈ Finset.range 131, stT106 (i+1)) + stT106 132 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 131
    simpa using h
  have hprev := st106_p131
  have hstep := st106_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p133 : ((515873640963/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT106 (i+1))
      = (∑ i ∈ Finset.range 132, stT106 (i+1)) + stT106 133 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 132
    simpa using h
  have hprev := st106_p132
  have hstep := st106_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p134 : ((2119947689751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT106 (i+1))
      = (∑ i ∈ Finset.range 133, stT106 (i+1)) + stT106 134 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 133
    simpa using h
  have hprev := st106_p133
  have hstep := st106_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p135 : ((57671430649/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT106 (i+1))
      = (∑ i ∈ Finset.range 134, stT106 (i+1)) + stT106 135 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 134
    simpa using h
  have hprev := st106_p134
  have hstep := st106_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p136 : ((78555796263/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT106 (i+1))
      = (∑ i ∈ Finset.range 135, stT106 (i+1)) + stT106 136 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 135
    simpa using h
  have hprev := st106_p135
  have hstep := st106_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p137 : ((2621771933431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT106 (i+1))
      = (∑ i ∈ Finset.range 136, stT106 (i+1)) + stT106 137 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 136
    simpa using h
  have hprev := st106_p136
  have hstep := st106_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p138 : ((5142018700757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT106 (i+1))
      = (∑ i ∈ Finset.range 137, stT106 (i+1)) + stT106 138 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 137
    simpa using h
  have hprev := st106_p137
  have hstep := st106_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p139 : ((47837326407/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT106 (i+1))
      = (∑ i ∈ Finset.range 138, stT106 (i+1)) + stT106 139 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 138
    simpa using h
  have hprev := st106_p138
  have hstep := st106_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p140 : ((1747664010513/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT106 (i+1))
      = (∑ i ∈ Finset.range 139, stT106 (i+1)) + stT106 140 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 139
    simpa using h
  have hprev := st106_p139
  have hstep := st106_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p141 : ((8248180851349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT106 (i+1))
      = (∑ i ∈ Finset.range 140, stT106 (i+1)) + stT106 141 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 140
    simpa using h
  have hprev := st106_p140
  have hstep := st106_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p142 : ((1671049719683/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT106 (i+1))
      = (∑ i ∈ Finset.range 141, stT106 (i+1)) + stT106 142 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 141
    simpa using h
  have hprev := st106_p141
  have hstep := st106_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p143 : ((8995365925913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT106 (i+1))
      = (∑ i ∈ Finset.range 142, stT106 (i+1)) + stT106 143 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 142
    simpa using h
  have hprev := st106_p142
  have hstep := st106_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p144 : ((4913999879763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT106 (i+1))
      = (∑ i ∈ Finset.range 143, stT106 (i+1)) + stT106 144 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 143
    simpa using h
  have hprev := st106_p143
  have hstep := st106_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p145 : ((521112012711/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT106 (i+1))
      = (∑ i ∈ Finset.range 144, stT106 (i+1)) + stT106 145 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 144
    simpa using h
  have hprev := st106_p144
  have hstep := st106_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p146 : ((2095847316593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT106 (i+1))
      = (∑ i ∈ Finset.range 145, stT106 (i+1)) + stT106 146 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 145
    simpa using h
  have hprev := st106_p145
  have hstep := st106_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p147 : ((498852219917/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT106 (i+1))
      = (∑ i ∈ Finset.range 146, stT106 (i+1)) + stT106 147 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 146
    simpa using h
  have hprev := st106_p146
  have hstep := st106_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p148 : ((229274984733/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT106 (i+1))
      = (∑ i ∈ Finset.range 147, stT106 (i+1)) + stT106 148 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 147
    simpa using h
  have hprev := st106_p147
  have hstep := st106_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p149 : ((1057310785533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT106 (i+1))
      = (∑ i ∈ Finset.range 148, stT106 (i+1)) + stT106 149 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 148
    simpa using h
  have hprev := st106_p148
  have hstep := st106_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p150 : ((818190445749/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT106 (i+1))
      = (∑ i ∈ Finset.range 149, stT106 (i+1)) + stT106 150 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 149
    simpa using h
  have hprev := st106_p149
  have hstep := st106_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p151 : ((4233811084569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT106 (i+1))
      = (∑ i ∈ Finset.range 150, stT106 (i+1)) + stT106 151 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 150
    simpa using h
  have hprev := st106_p150
  have hstep := st106_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p152 : ((9174546530523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT106 (i+1))
      = (∑ i ∈ Finset.range 151, stT106 (i+1)) + stT106 152 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 151
    simpa using h
  have hprev := st106_p151
  have hstep := st106_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p153 : ((9969494956767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT106 (i+1))
      = (∑ i ∈ Finset.range 152, stT106 (i+1)) + stT106 153 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 152
    simpa using h
  have hprev := st106_p152
  have hstep := st106_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p154 : ((10487027689691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT106 (i+1))
      = (∑ i ∈ Finset.range 153, stT106 (i+1)) + stT106 154 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 153
    simpa using h
  have hprev := st106_p153
  have hstep := st106_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p155 : ((10496142618903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT106 (i+1))
      = (∑ i ∈ Finset.range 154, stT106 (i+1)) + stT106 155 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 154
    simpa using h
  have hprev := st106_p154
  have hstep := st106_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p156 : ((9998742796371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT106 (i+1))
      = (∑ i ∈ Finset.range 155, stT106 (i+1)) + stT106 156 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 155
    simpa using h
  have hprev := st106_p155
  have hstep := st106_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p157 : ((9220413238143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT106 (i+1))
      = (∑ i ∈ Finset.range 156, stT106 (i+1)) + stT106 157 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 156
    simpa using h
  have hprev := st106_p156
  have hstep := st106_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p158 : ((8503952001177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT106 (i+1))
      = (∑ i ∈ Finset.range 157, stT106 (i+1)) + stT106 158 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 157
    simpa using h
  have hprev := st106_p157
  have hstep := st106_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p159 : ((8157386691073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT106 (i+1))
      = (∑ i ∈ Finset.range 158, stT106 (i+1)) + stT106 159 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 158
    simpa using h
  have hprev := st106_p158
  have hstep := st106_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p160 : ((1664796343061/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT106 (i+1))
      = (∑ i ∈ Finset.range 159, stT106 (i+1)) + stT106 160 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 159
    simpa using h
  have hprev := st106_p159
  have hstep := st106_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p161 : ((1785548665797/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT106 (i+1))
      = (∑ i ∈ Finset.range 160, stT106 (i+1)) + stT106 161 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 160
    simpa using h
  have hprev := st106_p160
  have hstep := st106_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p162 : ((9712696865927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT106 (i+1))
      = (∑ i ∈ Finset.range 161, stT106 (i+1)) + stT106 162 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 161
    simpa using h
  have hprev := st106_p161
  have hstep := st106_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p163 : ((10354353640307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT106 (i+1))
      = (∑ i ∈ Finset.range 162, stT106 (i+1)) + stT106 163 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 162
    simpa using h
  have hprev := st106_p162
  have hstep := st106_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p164 : ((10593866939343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT106 (i+1))
      = (∑ i ∈ Finset.range 163, stT106 (i+1)) + stT106 164 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 163
    simpa using h
  have hprev := st106_p163
  have hstep := st106_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p165 : ((10339665217871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT106 (i+1))
      = (∑ i ∈ Finset.range 164, stT106 (i+1)) + stT106 165 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 164
    simpa using h
  have hprev := st106_p164
  have hstep := st106_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p166 : ((484902572803/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT106 (i+1))
      = (∑ i ∈ Finset.range 165, stT106 (i+1)) + stT106 166 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 165
    simpa using h
  have hprev := st106_p165
  have hstep := st106_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p167 : ((2231193637407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT106 (i+1))
      = (∑ i ∈ Finset.range 166, stT106 (i+1)) + stT106 167 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 166
    simpa using h
  have hprev := st106_p166
  have hstep := st106_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p168 : ((4160419378599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT106 (i+1))
      = (∑ i ∈ Finset.range 167, stT106 (i+1)) + stT106 168 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 167
    simpa using h
  have hprev := st106_p167
  have hstep := st106_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p169 : ((8115641003331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT106 (i+1))
      = (∑ i ∈ Finset.range 168, stT106 (i+1)) + stT106 169 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 168
    simpa using h
  have hprev := st106_p168
  have hstep := st106_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p170 : ((8382476982499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT106 (i+1))
      = (∑ i ∈ Finset.range 169, stT106 (i+1)) + stT106 170 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 169
    simpa using h
  have hprev := st106_p169
  have hstep := st106_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p171 : ((9016297501831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT106 (i+1))
      = (∑ i ∈ Finset.range 170, stT106 (i+1)) + stT106 171 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 170
    simpa using h
  have hprev := st106_p170
  have hstep := st106_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p172 : ((9778524917107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT106 (i+1))
      = (∑ i ∈ Finset.range 171, stT106 (i+1)) + stT106 172 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 171
    simpa using h
  have hprev := st106_p171
  have hstep := st106_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p173 : ((10388819371737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT106 (i+1))
      = (∑ i ∈ Finset.range 172, stT106 (i+1)) + stT106 173 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 172
    simpa using h
  have hprev := st106_p172
  have hstep := st106_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p174 : ((10627951530563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT106 (i+1))
      = (∑ i ∈ Finset.range 173, stT106 (i+1)) + stT106 174 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 173
    simpa using h
  have hprev := st106_p173
  have hstep := st106_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p175 : ((5207152036611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT106 (i+1))
      = (∑ i ∈ Finset.range 174, stT106 (i+1)) + stT106 175 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 174
    simpa using h
  have hprev := st106_p174
  have hstep := st106_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p176 : ((9828301956821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT106 (i+1))
      = (∑ i ∈ Finset.range 175, stT106 (i+1)) + stT106 176 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 175
    simpa using h
  have hprev := st106_p175
  have hstep := st106_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p177 : ((2269751715071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT106 (i+1))
      = (∑ i ∈ Finset.range 176, stT106 (i+1)) + stT106 177 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 176
    simpa using h
  have hprev := st106_p176
  have hstep := st106_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p178 : ((2106888904919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT106 (i+1))
      = (∑ i ∈ Finset.range 177, stT106 (i+1)) + stT106 178 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 177
    simpa using h
  have hprev := st106_p177
  have hstep := st106_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p179 : ((404800547427/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT106 (i+1))
      = (∑ i ∈ Finset.range 178, stT106 (i+1)) + stT106 179 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 178
    simpa using h
  have hprev := st106_p178
  have hstep := st106_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p180 : ((819333791373/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT106 (i+1))
      = (∑ i ∈ Finset.range 179, stT106 (i+1)) + stT106 180 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 179
    simpa using h
  have hprev := st106_p179
  have hstep := st106_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p181 : ((2170611358667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT106 (i+1))
      = (∑ i ∈ Finset.range 180, stT106 (i+1)) + stT106 181 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 180
    simpa using h
  have hprev := st106_p180
  have hstep := st106_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p182 : ((9397096196801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT106 (i+1))
      = (∑ i ∈ Finset.range 181, stT106 (i+1)) + stT106 182 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 181
    simpa using h
  have hprev := st106_p181
  have hstep := st106_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p183 : ((10100521159097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT106 (i+1))
      = (∑ i ∈ Finset.range 182, stT106 (i+1)) + stT106 183 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 182
    simpa using h
  have hprev := st106_p182
  have hstep := st106_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p184 : ((5282254722781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT106 (i+1))
      = (∑ i ∈ Finset.range 183, stT106 (i+1)) + stT106 184 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 183
    simpa using h
  have hprev := st106_p183
  have hstep := st106_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p185 : ((1330309769381/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT106 (i+1))
      = (∑ i ∈ Finset.range 184, stT106 (i+1)) + stT106 185 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 184
    simpa using h
  have hprev := st106_p184
  have hstep := st106_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p186 : ((644597238613/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT106 (i+1))
      = (∑ i ∈ Finset.range 185, stT106 (i+1)) + stT106 186 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 185
    simpa using h
  have hprev := st106_p185
  have hstep := st106_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p187 : ((1210660875937/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT106 (i+1))
      = (∑ i ∈ Finset.range 186, stT106 (i+1)) + stT106 187 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 186
    simpa using h
  have hprev := st106_p186
  have hstep := st106_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p188 : ((8956212165971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT106 (i+1))
      = (∑ i ∈ Finset.range 187, stT106 (i+1)) + stT106 188 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 187
    simpa using h
  have hprev := st106_p187
  have hstep := st106_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p189 : ((8351905699859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT106 (i+1))
      = (∑ i ∈ Finset.range 188, stT106 (i+1)) + stT106 189 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 188
    simpa using h
  have hprev := st106_p188
  have hstep := st106_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p190 : ((8055348113707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT106 (i+1))
      = (∑ i ∈ Finset.range 189, stT106 (i+1)) + stT106 190 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 189
    simpa using h
  have hprev := st106_p189
  have hstep := st106_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p191 : ((8152966205621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT106 (i+1))
      = (∑ i ∈ Finset.range 190, stT106 (i+1)) + stT106 191 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 190
    simpa using h
  have hprev := st106_p190
  have hstep := st106_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p192 : ((4305849304307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT106 (i+1))
      = (∑ i ∈ Finset.range 191, stT106 (i+1)) + stT106 192 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 191
    simpa using h
  have hprev := st106_p191
  have hstep := st106_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p193 : ((4646173517417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT106 (i+1))
      = (∑ i ∈ Finset.range 192, stT106 (i+1)) + stT106 193 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 192
    simpa using h
  have hprev := st106_p192
  have hstep := st106_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p194 : ((1249187473991/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT106 (i+1))
      = (∑ i ∈ Finset.range 193, stT106 (i+1)) + stT106 194 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 193
    simpa using h
  have hprev := st106_p193
  have hstep := st106_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p195 : ((5255882549947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT106 (i+1))
      = (∑ i ∈ Finset.range 194, stT106 (i+1)) + stT106 195 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 194
    simpa using h
  have hprev := st106_p194
  have hstep := st106_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p196 : ((10700218482869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT106 (i+1))
      = (∑ i ∈ Finset.range 195, stT106 (i+1)) + stT106 196 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 195
    simpa using h
  have hprev := st106_p195
  have hstep := st106_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p197 : ((2627125449723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT106 (i+1))
      = (∑ i ∈ Finset.range 196, stT106 (i+1)) + stT106 197 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 196
    simpa using h
  have hprev := st106_p196
  have hstep := st106_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p198 : ((4997088208581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT106 (i+1))
      = (∑ i ∈ Finset.range 197, stT106 (i+1)) + stT106 198 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 197
    simpa using h
  have hprev := st106_p197
  have hstep := st106_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p199 : ((46517772543/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT106 (i+1))
      = (∑ i ∈ Finset.range 198, stT106 (i+1)) + stT106 199 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 198
    simpa using h
  have hprev := st106_p198
  have hstep := st106_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_p200 : ((1078594933759/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT106 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT106 (i+1))
      = (∑ i ∈ Finset.range 199, stT106 (i+1)) + stT106 200 := by
    have h := Finset.sum_range_succ (fun i => stT106 (i+1)) 199
    simpa using h
  have hprev := st106_p199
  have hstep := st106_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st106_s200 :
    |Real.sin (((106 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))
      - ((-149499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -56759/80000) (δ := 343/50000000) (ψ := -1027087/1000000) 106 90
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 106`** (evaluated boundary). -/
theorem station_106_sign : hardyG (((106:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower_eval 106 200 (by norm_num) (by norm_num)
    ((-1027087/1000000 : ℚ) : ℝ)
  have hchain := st106_p200
  have hbridge : (∑ i ∈ Finset.range 200, stT106 (i+1))
      = ∑ i ∈ Finset.range 200,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((106:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-1027087/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_200
  have hsh := rpow_half_shifts (N := 200) (by norm_num)
  have hcosb := abs_le.mp st106_c200
  have hsinb := abs_le.mp st106_s200
  have hbdy_lo : ((1137224084127/28090625000000 : ℚ) : ℝ)
      ≤ ((200:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos ((((106:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((-1027087/1000000 : ℚ) : ℝ))) / 2
          - (((106:ℕ)):ℝ)
            * Real.sin ((((106:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((-1027087/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + (((106:ℕ)):ℝ) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((106:ℝ) * Real.log ((200:ℝ)) - ((-1027087/1000000 : ℚ) : ℝ))) / 2
        - (106:ℝ) * Real.sin ((106:ℝ) * Real.log ((200:ℝ)) - ((-1027087/1000000 : ℚ) : ℝ))
        ≥ ((3216559/100000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (200:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + (106:ℝ) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((3216559/100000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (200:ℝ) * (353553/5000000)
          * ((3216559/100000 : ℚ) : ℝ)
        ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ)))
          * ((3216559/100000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((200:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((106:ℕ)):ℝ)+1) * ((((106:ℕ)):ℝ)+2) / 8
        * (((200:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((200:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((302704728523/800000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1078594933759/1250000000000 : ℚ) : ℝ) + ((1137224084127/28090625000000 : ℚ) : ℝ)
      - ((302704728523/800000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-1027087/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((106:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-1027087/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((106:ℕ)):ℝ))).re
      - Real.sin ((-1027087/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((106:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((106:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((106:ℕ)):ℝ)
      = ((((106:ℕ)):ℝ) * (Real.log (((106:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((106:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_106
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
  have hθwin : |(((-1027087/1000000 : ℚ) : ℝ) + ((16:ℤ)) * (2*Real.pi) - Real.pi) - theta (((106:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((106:ℕ)):ℝ))
    (φ := ((-1027087/1000000 : ℚ) : ℝ) + ((16:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-1027087/1000000 : ℚ) : ℝ) + ((16:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-1027087/1000000 : ℚ)) : ℝ) - Real.pi) + ((16:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-1027087/1000000 : ℚ)) : ℝ) - Real.pi) 16).1,
    (cos_sin_shift ((((-1027087/1000000 : ℚ)) : ℝ) - Real.pi) 16).2]
  exact cos_sin_flip ((-1027087/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_106_sign
end AxiomAudit
