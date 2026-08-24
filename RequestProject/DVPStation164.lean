import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 164` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT164 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((164 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))

theorem st164_c1 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((968841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312861/5000000) (δ := 201/1000000000) (ψ := -250289/1000000) 164 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t1 : ((968791/1000000 : ℚ) : ℝ) ≤ stT164 1 := by
  have hc : ((968791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((968791/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((968791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c2 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((13511/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414543/2000000) (δ := 517/62500000) (ψ := -250289/1000000) 164 18
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t2 : ((9553011517/20000000000 : ℚ) : ℝ) ≤ stT164 2 := by
  have hc : ((1351/2000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9553011517/20000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((1351/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c3 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-13571/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -447419/1000000) (δ := 8293/1000000000) (ψ := -250289/1000000) 164 29
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t3 : ((-626962011279/5000000000000 : ℚ) : ℝ) ≤ stT164 3 := by
  have hc : ((-108593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-626962011279/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-108593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c4 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((81093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 219983/625000) (δ := 8343/1000000000) (ψ := -250289/1000000) 164 36
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t4 : ((20267/250000 : ℚ) : ℝ) ≤ stT164 4 := by
  have hc : ((20267/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20267/250000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((20267/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c5 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((14907/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30433/400000) (δ := 8303/1000000000) (ψ := -250289/1000000) 164 42
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t5 : ((426640784573/1000000000000 : ℚ) : ℝ) ≤ stT164 5 := by
  have hc : ((476999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426640784573/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((476999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c6 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((70441/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3027177/10000000) (δ := 2091/250000000) (ψ := -250289/1000000) 164 47
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t6 : ((143766644871/1000000000000 : ℚ) : ℝ) ≤ stT164 6 := by
  have hc : ((70431/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143766644871/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((70431/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c7 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((486343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2657243/10000000) (δ := 1667/200000000) (ψ := -250289/1000000) 164 51
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t7 : ((459503604923/2500000000000 : ℚ) : ℝ) ≤ stT164 7 := by
  have hc : ((486293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459503604923/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((486293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c8 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-202007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2483371/5000000) (δ := 8389/1000000000) (ψ := -250289/1000000) 164 54
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t8 : ((-22321593909/156250000000 : ℚ) : ℝ) ≤ stT164 8 := by
  have hc : ((-12627/31250 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22321593909/156250000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-12627/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c9 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-193123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3066941/5000000) (δ := 8311/1000000000) (ψ := -250289/1000000) 164 57
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t9 : ((-643785128757/2500000000000 : ℚ) : ℝ) ≤ stT164 9 := by
  have hc : ((-386271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643785128757/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-386271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c10 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((79343/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2207797/10000000) (δ := 1029/125000000) (ψ := -250289/1000000) 164 60
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t10 : ((1003539119119/5000000000000 : ℚ) : ℝ) ≤ stT164 10 := by
  have hc : ((317347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1003539119119/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((317347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c11 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-69237/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5838911/10000000) (δ := 8249/1000000000) (ψ := -250289/1000000) 164 63
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t11 : ((-52193130897/250000000000 : ℚ) : ℝ) ≤ stT164 11 := by
  have hc : ((-34621/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52193130897/250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-34621/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c12 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((806809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1580163/10000000) (δ := 523/62500000) (ψ := -250289/1000000) 164 65
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t12 : ((2328912350009/10000000000000 : ℚ) : ℝ) ≤ stT164 12 := by
  have hc : ((806759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2328912350009/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((806759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c13 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((19949/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -178583/10000000) (δ := 411/50000000) (ψ := -250289/1000000) 164 67
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t13 : ((27662889/100000000 : ℚ) : ℝ) ≤ stT164 13 := by
  have hc : ((4987/5000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27662889/100000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((4987/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c14 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((442549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1210229/10000000) (δ := 8397/1000000000) (ψ := -250289/1000000) 164 69
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t14 : ((73918434543/312500000000 : ℚ) : ℝ) ≤ stT164 14 := by
  have hc : ((110631/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73918434543/312500000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((110631/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c15 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-32817/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4339067/10000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 71
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t15 : ((-84758952903/2000000000000 : ℚ) : ℝ) ≤ stT164 15 := by
  have hc : ((-32827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84758952903/2000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-32827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c16 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-838599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1282751/2000000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 72
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t16 : ((-2096623338649/10000000000000 : ℚ) : ℝ) ≤ stT164 16 := by
  have hc : ((-838649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2096623338649/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-838649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c17 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((998293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73043/5000000) (δ := 827/100000000) (ψ := -250289/1000000) 164 74
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t17 : ((605273662377/2500000000000 : ℚ) : ℝ) ≤ stT164 17 := by
  have hc : ((998243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((605273662377/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((998243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c18 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-24851/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1516179/2000000) (δ := 103/12500000) (ψ := -250289/1000000) 164 75
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t18 : ((-234309299407/1000000000000 : ℚ) : ℝ) ≤ stT164 18 := by
  have hc : ((-99409/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234309299407/1000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-99409/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c19 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((392843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41687/250000) (δ := 8349/1000000000) (ψ := -250289/1000000) 164 77
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t19 : ((450593082213/2500000000000 : ℚ) : ℝ) ≤ stT164 19 := by
  have hc : ((196409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450593082213/2500000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((196409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c20 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((108657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365481/1000000) (δ := 8241/1000000000) (ψ := -250289/1000000) 164 78
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t20 : ((242852528669/10000000000000 : ℚ) : ℝ) ≤ stT164 20 := by
  have hc : ((108607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242852528669/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((108607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c21 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-3997/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3878567/5000000) (δ := 1047/125000000) (ψ := -250289/1000000) 164 80
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t21 : ((-21806514747/100000000000 : ℚ) : ℝ) ≤ stT164 21 := by
  have hc : ((-9993/10000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21806514747/100000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-9993/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c22 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-184893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2195949/5000000) (δ := 13/1562500) (ψ := -250289/1000000) 164 81
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t22 : ((-49287494443/1250000000000 : ℚ) : ℝ) ≤ stT164 22 := by
  have hc : ((-184943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49287494443/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-184943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c23 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((45737/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1874623/10000000) (δ := 8213/1000000000) (ψ := -250289/1000000) 164 82
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t23 : ((95361715053/625000000000 : ℚ) : ℝ) ≤ stT164 23 := by
  have hc : ((365871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95361715053/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((365871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c24 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((499291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2663/200000) (δ := 8297/1000000000) (ψ := -250289/1000000) 164 83
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t24 : ((509561114553/2500000000000 : ℚ) : ℝ) ≤ stT164 24 := by
  have hc : ((249633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((509561114553/2500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((249633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c25 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((117059/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 447953/5000000) (δ := 4199/500000000) (ψ := -250289/1000000) 164 84
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t25 : ((468211/2500000 : ℚ) : ℝ) ≤ stT164 25 := by
  have hc : ((468211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468211/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((468211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c26 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((109253/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126843/1000000) (δ := 8291/1000000000) (ψ := -250289/1000000) 164 85
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t26 : ((857001861907/5000000000000 : ℚ) : ℝ) ≤ stT164 26 := by
  have hc : ((436987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((857001861907/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((436987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c27 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((915681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103399/1000000) (δ := 8219/1000000000) (ψ := -250289/1000000) 164 86
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t27 : ((3524263719/20000000000 : ℚ) : ℝ) ≤ stT164 27 := by
  have hc : ((915631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3524263719/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((915631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c28 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((497759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14799/625000) (δ := 4163/500000000) (ψ := -250289/1000000) 164 87
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t28 : ((235157165837/1250000000000 : ℚ) : ℝ) ≤ stT164 28 := by
  have hc : ((248867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235157165837/1250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((248867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c29 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((453751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1083747/10000000) (δ := 837/100000000) (ψ := -250289/1000000) 164 88
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t29 : ((421273928439/2500000000000 : ℚ) : ℝ) ≤ stT164 29 := by
  have hc : ((226863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421273928439/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((226863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c30 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((100559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -578419/2000000) (δ := 8263/1000000000) (ψ := -250289/1000000) 164 89
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t30 : ((367143734913/5000000000000 : ℚ) : ℝ) ≤ stT164 30 := by
  have hc : ((201093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367143734913/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((201093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c31 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-47211/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5156199/10000000) (δ := 1031/125000000) (ψ := -250289/1000000) 164 90
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t31 : ((-2650077677/31250000000 : ℚ) : ℝ) ≤ stT164 31 := by
  have hc : ((-2951/6250 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2650077677/31250000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-2951/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c32 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-249999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1569439/2000000) (δ := 1671/200000000) (ψ := -250289/1000000) 164 91
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t32 : ((-883924158641/5000000000000 : ℚ) : ℝ) ≤ stT164 32 := by
  have hc : ((-500023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-883924158641/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-500023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c33 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-330533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4769161/10000000) (δ := 1671/200000000) (ψ := -250289/1000000) 164 91
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t33 : ((-575471282991/10000000000000 : ℚ) : ℝ) ≤ stT164 33 := by
  have hc : ((-330583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575471282991/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-330583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c34 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((173527/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1300927/10000000) (δ := 8341/1000000000) (ψ := -250289/1000000) 164 92
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t34 : ((59515810449/400000000000 : ℚ) : ℝ) ≤ stT164 34 := by
  have hc : ((173517/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59515810449/400000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((173517/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c35 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((266411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2522161/10000000) (δ := 4117/500000000) (ψ := -250289/1000000) 164 93
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t35 : ((56284298361/625000000000 : ℚ) : ℝ) ≤ stT164 35 := by
  have hc : ((133193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56284298361/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((133193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c36 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-891763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1336011/2000000) (δ := 2069/250000000) (ψ := -250289/1000000) 164 94
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t36 : ((-1486355297271/10000000000000 : ℚ) : ℝ) ≤ stT164 36 := by
  have hc : ((-891813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1486355297271/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-891813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c37 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-124001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910707/2000000) (δ := 2069/250000000) (ψ := -250289/1000000) 164 94
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t37 : ((-10194875187/250000000000 : ℚ) : ℝ) ≤ stT164 37 := by
  have hc : ((-62013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10194875187/250000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-62013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c38 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((498057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110233/5000000) (δ := 131/15625000) (ψ := -250289/1000000) 164 95
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t38 : ((25247327589/156250000000 : ℚ) : ℝ) ≤ stT164 38 := by
  have hc : ((31127/31250 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25247327589/156250000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((31127/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c39 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-102929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211139/400000) (δ := 1039/125000000) (ψ := -250289/1000000) 164 96
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t39 : ((-82417183899/1000000000000 : ℚ) : ℝ) ≤ stT164 39 := by
  have hc : ((-102939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82417183899/1000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-102939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c40 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-226413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5101823/10000000) (δ := 1039/125000000) (ψ := -250289/1000000) 164 96
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t40 : ((-179014976441/2500000000000 : ℚ) : ℝ) ≤ stT164 40 := by
  have hc : ((-113219/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179014976441/2500000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-113219/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c41 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((490729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241087/5000000) (δ := 1641/200000000) (ψ := -250289/1000000) 164 97
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t41 : ((47896912053/312500000000 : ℚ) : ℝ) ≤ stT164 41 := by
  have hc : ((30669/31250 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47896912053/312500000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((30669/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c42 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-815303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6310121/10000000) (δ := 1661/200000000) (ψ := -250289/1000000) 164 98
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t42 : ((-629058700501/5000000000000 : ℚ) : ℝ) ≤ stT164 42 := by
  have hc : ((-815353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629058700501/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-815353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c43 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((116831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 417173/1250000) (δ := 1661/200000000) (ψ := -250289/1000000) 164 98
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t43 : ((17812739791/500000000000 : ℚ) : ℝ) ≤ stT164 43 := by
  have hc : ((58403/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17812739791/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((58403/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c44 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((11963/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -588977/2000000) (δ := 8391/1000000000) (ψ := -250289/1000000) 164 99
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t44 : ((72130147487/1250000000000 : ℚ) : ℝ) ≤ stT164 44 := by
  have hc : ((191383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72130147487/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((191383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c45 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-40283/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6268963/10000000) (δ := 8391/1000000000) (ψ := -250289/1000000) 164 99
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t45 : ((-15013519569/125000000000 : ℚ) : ℝ) ≤ stT164 45 := by
  have hc : ((-80571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15013519569/125000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-80571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c46 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((197081/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -427651/10000000) (δ := 2071/250000000) (ψ := -250289/1000000) 164 100
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t46 : ((290565226749/2000000000000 : ℚ) : ℝ) ≤ stT164 46 := by
  have hc : ((197071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290565226749/2000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((197071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c47 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-244277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7318031/10000000) (δ := 8227/1000000000) (ψ := -250289/1000000) 164 101
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t47 : ((-14253315167/100000000000 : ℚ) : ℝ) ≤ stT164 47 := by
  have hc : ((-488579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14253315167/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-488579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c48 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((865051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1313863/10000000) (δ := 8227/1000000000) (ψ := -250289/1000000) 164 101
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t48 : ((9988166547/80000000000 : ℚ) : ℝ) ≤ stT164 48 := by
  have hc : ((865001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9988166547/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((865001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c49 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-144207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1485057/2500000) (δ := 4167/500000000) (ψ := -250289/1000000) 164 102
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t49 : ((-51506092031/500000000000 : ℚ) : ℝ) ≤ stT164 49 := by
  have hc : ((-144217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51506092031/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-144217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c50 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((592073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58573/250000) (δ := 4167/500000000) (ψ := -250289/1000000) 164 102
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t50 : ((837246622899/10000000000000 : ℚ) : ℝ) ≤ stT164 50 := by
  have hc : ((592023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((837246622899/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((592023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c51 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-503457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2622989/5000000) (δ := 4181/500000000) (ψ := -250289/1000000) 164 103
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t51 : ((-705051285467/10000000000000 : ℚ) : ℝ) ≤ stT164 51 := by
  have hc : ((-503507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-705051285467/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-503507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c52 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((465871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2715443/10000000) (δ := 4181/500000000) (ψ := -250289/1000000) 164 103
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t52 : ((2583909087/40000000000 : ℚ) : ℝ) ≤ stT164 52 := by
  have hc : ((465821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2583909087/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((465821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c53 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-481449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2591379/5000000) (δ := 1651/200000000) (ψ := -250289/1000000) 164 104
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t53 : ((-330694957697/5000000000000 : ℚ) : ℝ) ≤ stT164 53 := by
  have hc : ((-481499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330694957697/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-481499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c54 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((546681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2481003/10000000) (δ := 1651/200000000) (ψ := -250289/1000000) 164 104
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t54 : ((743870223837/10000000000000 : ℚ) : ℝ) ≤ stT164 54 := by
  have hc : ((546631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((743870223837/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((546631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c55 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-652391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5703829/10000000) (δ := 1651/200000000) (ψ := -250289/1000000) 164 105
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t55 : ((-2199378611/25000000000 : ℚ) : ℝ) ≤ stT164 55 := by
  have hc : ((-652441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2199378611/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-652441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c56 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((390821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420939/2500000) (δ := 1651/200000000) (ψ := -250289/1000000) 164 105
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t56 : ((65277879947/625000000000 : ℚ) : ℝ) ≤ stT164 56 := by
  have hc : ((97699/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65277879947/625000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((97699/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c57 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-45351/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6767371/10000000) (δ := 8363/1000000000) (ψ := -250289/1000000) 164 106
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t57 : ((-120144414831/1000000000000 : ℚ) : ℝ) ≤ stT164 57 := by
  have hc : ((-90707/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120144414831/1000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-90707/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c58 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((494731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363267/10000000) (δ := 8363/1000000000) (ψ := -250289/1000000) 164 106
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t58 : ((40598789949/312500000000 : ℚ) : ℝ) ≤ stT164 58 := by
  have hc : ((247353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40598789949/312500000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((247353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c59 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-981471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7371971/10000000) (δ := 8363/1000000000) (ψ := -250289/1000000) 164 106
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t59 : ((-127783237469/1000000000000 : ℚ) : ℝ) ≤ stT164 59 := by
  have hc : ((-981521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127783237469/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-981521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c60 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((837539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -722541/5000000) (δ := 8333/1000000000) (ψ := -250289/1000000) 164 107
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t60 : ((540596637033/5000000000000 : ℚ) : ℝ) ≤ stT164 60 := by
  have hc : ((837489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540596637033/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((837489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c61 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-532859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5331931/10000000) (δ := 8333/1000000000) (ψ := -250289/1000000) 164 107
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t61 : ((-682320163421/10000000000000 : ℚ) : ℝ) ≤ stT164 61 := by
  have hc : ((-532909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682320163421/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-532909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c62 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((17399/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3709227/10000000) (δ := 4113/500000000) (ψ := -250289/1000000) 164 108
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t62 : ((22084047389/2000000000000 : ℚ) : ℝ) ≤ stT164 62 := by
  have hc : ((17389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22084047389/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((17389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c63 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((208627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2850937/10000000) (δ := 4113/500000000) (ψ := -250289/1000000) 164 108
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t63 : ((131406848181/2500000000000 : ℚ) : ℝ) ≤ stT164 63 := by
  have hc : ((104301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131406848181/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((104301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c64 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-417819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6400223/10000000) (δ := 2071/250000000) (ψ := -250289/1000000) 164 109
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t64 : ((-130576354461/1250000000000 : ℚ) : ℝ) ≤ stT164 64 := by
  have hc : ((-104461/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130576354461/1250000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-104461/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c65 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((999849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43501/10000000) (δ := 2071/250000000) (ψ := -250289/1000000) 164 109
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t65 : ((1240097690253/10000000000000 : ℚ) : ℝ) ≤ stT164 65 := by
  have hc : ((999799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1240097690253/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((999799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c66 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-792973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3108087/5000000) (δ := 2071/250000000) (ψ := -250289/1000000) 164 109
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t66 : ((-195228781209/2000000000000 : ℚ) : ℝ) ≤ stT164 66 := by
  have hc : ((-793023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195228781209/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-793023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c67 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((23799/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2661/8000) (δ := 8391/1000000000) (ψ := -250289/1000000) 164 110
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t67 : ((7267246759/250000000000 : ℚ) : ℝ) ≤ stT164 67 := by
  have hc : ((11897/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7267246759/250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((11897/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c68 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((45433/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2747941/10000000) (δ := 8391/1000000000) (ψ := -250289/1000000) 164 110
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t68 : ((6886192023/125000000000 : ℚ) : ℝ) ≤ stT164 68 := by
  have hc : ((11357/25000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6886192023/125000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((11357/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c69 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-938759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1394903/2000000) (δ := 1661/200000000) (ψ := -250289/1000000) 164 111
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t69 : ((-1130193663931/10000000000000 : ℚ) : ℝ) ≤ stT164 69 := by
  have hc : ((-938809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1130193663931/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-938809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c70 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((908941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268787/2500000) (δ := 1661/200000000) (ψ := -250289/1000000) 164 111
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t70 : ((271582993037/2500000000000 : ℚ) : ℝ) ≤ stT164 70 := by
  have hc : ((908891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271582993037/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((908891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c71 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-159853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2370269/5000000) (δ := 1661/200000000) (ψ := -250289/1000000) 164 111
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t71 : ((-47435083149/1250000000000 : ℚ) : ℝ) ≤ stT164 71 := by
  have hc : ((-79939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47435083149/1250000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-79939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c72 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-498979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2616521/5000000) (δ := 4103/500000000) (ψ := -250289/1000000) 164 112
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t72 : ((-36756979053/625000000000 : ℚ) : ℝ) ≤ stT164 72 := by
  have hc : ((-499029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36756979053/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-499029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c73 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((985773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 422211/10000000) (δ := 4103/500000000) (ψ := -250289/1000000) 164 112
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t73 : ((1153701042153/10000000000000 : ℚ) : ℝ) ≤ stT164 73 := by
  have hc : ((985723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1153701042153/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((985723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c74 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-737531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6000507/10000000) (δ := 4103/500000000) (ψ := -250289/1000000) 164 112
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t74 : ((-857420948137/10000000000000 : ℚ) : ℝ) ≤ stT164 74 := by
  have hc : ((-737581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-857420948137/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-737581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c75 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-110571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -840797/2000000) (δ := 8313/1000000000) (ψ := -250289/1000000) 164 113
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t75 : ((-127734179321/10000000000000 : ℚ) : ℝ) ≤ stT164 75 := by
  have hc : ((-110621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127734179321/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-110621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c76 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((882041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1226547/10000000) (δ := 8313/1000000000) (ψ := -250289/1000000) 164 113
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t76 : ((505856236149/5000000000000 : ℚ) : ℝ) ≤ stT164 76 := by
  have hc : ((881991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((505856236149/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((881991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c77 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-874133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1646527/2500000) (δ := 8313/1000000000) (ψ := -250289/1000000) 164 113
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t77 : ((-498112095949/5000000000000 : ℚ) : ℝ) ≤ stT164 77 := by
  have hc : ((-874183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498112095949/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-874183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c78 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((19101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1915731/5000000) (δ := 8383/1000000000) (ψ := -250289/1000000) 164 114
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t78 : ((5399829013/1250000000000 : ℚ) : ℝ) ≤ stT164 78 := by
  have hc : ((4769/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5399829013/1250000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((4769/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c79 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((16981/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173941/1250000) (δ := 8383/1000000000) (ψ := -250289/1000000) 164 114
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t79 : ((955198863/10000000000 : ℚ) : ℝ) ≤ stT164 79 := by
  have hc : ((849/1000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((955198863/10000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((849/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c80 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-173359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1637209/2500000) (δ := 8383/1000000000) (ψ := -250289/1000000) 164 114
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t80 : ((-96916218273/1000000000000 : ℚ) : ℝ) ≤ stT164 80 := by
  have hc : ((-173369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96916218273/1000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-173369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c81 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-3471/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2032951/5000000) (δ := 2069/250000000) (ψ := -250289/1000000) 164 115
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t81 : ((-3860141977/625000000000 : ℚ) : ℝ) ≤ stT164 81 := by
  have hc : ((-27793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3860141977/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-27793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c82 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((926447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 964839/10000000) (δ := 2069/250000000) (ψ := -250289/1000000) 164 115
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t82 : ((204606820611/2000000000000 : ℚ) : ℝ) ≤ stT164 82 := by
  have hc : ((926397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204606820611/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((926397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c83 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-719477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5934613/10000000) (δ := 2069/250000000) (ψ := -250289/1000000) 164 115
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t83 : ((-789783774861/10000000000000 : ℚ) : ℝ) ≤ stT164 83 := by
  have hc : ((-719527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-789783774861/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-719527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c84 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-182883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4863129/10000000) (δ := 16569/1000000000) (ψ := -250289/1000000) 164 116
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t84 : ((-4989227243/125000000000 : ℚ) : ℝ) ≤ stT164 84 := by
  have hc : ((-45727/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4989227243/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-45727/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c85 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((99999/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2751/2500000) (δ := 4117/500000000) (ψ := -250289/1000000) 164 116
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t85 : ((13557336511/125000000000 : ℚ) : ℝ) ≤ stT164 85 := by
  have hc : ((49997/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13557336511/125000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((49997/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c86 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-336263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1196089/2500000) (δ := 4117/500000000) (ψ := -250289/1000000) 164 116
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t86 : ((-45331965583/1250000000000 : ℚ) : ℝ) ≤ stT164 86 := by
  have hc : ((-336313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45331965583/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-336313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c87 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-784977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3091819/5000000) (δ := 4171/500000000) (ψ := -250289/1000000) 164 117
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t87 : ((-841637652051/10000000000000 : ℚ) : ℝ) ≤ stT164 87 := by
  have hc : ((-785027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-841637652051/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-785027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c88 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((103227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1497871/10000000) (δ := 4171/500000000) (ψ := -250289/1000000) 164 117
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t88 : ((440134516649/5000000000000 : ℚ) : ℝ) ≤ stT164 88 := by
  have hc : ((412883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440134516649/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((412883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c89 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((311553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 783731/2500000) (δ := 4171/500000000) (ψ := -250289/1000000) 164 117
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t89 : ((330192245491/10000000000000 : ℚ) : ℝ) ≤ stT164 89 := by
  have hc : ((311503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330192245491/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((311503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c90 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-998477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7715977/10000000) (δ := 4171/500000000) (ψ := -250289/1000000) 164 117
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t90 : ((-1052540321011/10000000000000 : ℚ) : ℝ) ≤ stT164 90 := by
  have hc : ((-998527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1052540321011/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-998527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c91 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((185103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -865387/2500000) (δ := 16449/1000000000) (ψ := -250289/1000000) 164 118
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t91 : ((48497024763/2500000000000 : ℚ) : ℝ) ≤ stT164 91 := by
  have hc : ((185053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48497024763/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((185053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c92 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((918017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 509681/5000000) (δ := 4177/500000000) (ψ := -250289/1000000) 164 118
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t92 : ((239261672781/2500000000000 : ℚ) : ℝ) ≤ stT164 92 := by
  have hc : ((917967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239261672781/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((917967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c93 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-114563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5451831/10000000) (δ := 4177/500000000) (ψ := -250289/1000000) 164 118
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t93 : ((-14850837687/250000000000 : ℚ) : ℝ) ≤ stT164 93 := by
  have hc : ((-114573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14850837687/250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-114573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c94 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-701591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5871059/10000000) (δ := 8247/1000000000) (ψ := -250289/1000000) 164 119
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t94 : ((-361843981751/5000000000000 : ℚ) : ℝ) ≤ stT164 94 := by
  have hc : ((-701641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361843981751/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-701641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c95 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((817949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766199/5000000) (δ := 8247/1000000000) (ψ := -250289/1000000) 164 119
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t95 : ((419573190111/5000000000000 : ℚ) : ℝ) ≤ stT164 95 := by
  have hc : ((817899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419573190111/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((817899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c96 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((449729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 552167/2000000) (δ := 8247/1000000000) (ψ := -250289/1000000) 164 119
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t96 : ((22947569049/500000000000 : ℚ) : ℝ) ≤ stT164 96 := by
  have hc : ((449679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22947569049/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((449679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c97 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-943499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7009583/10000000) (δ := 8247/1000000000) (ψ := -250289/1000000) 164 119
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t97 : ((-958029646503/10000000000000 : ℚ) : ℝ) ≤ stT164 97 := by
  have hc : ((-943549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-958029646503/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-943549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c98 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-112279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -898643/2000000) (δ := 8263/1000000000) (ψ := -250289/1000000) 164 120
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t98 : ((-7090263907/312500000000 : ℚ) : ℝ) ≤ stT164 98 := by
  have hc : ((-7019/31250 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7090263907/312500000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-7019/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c99 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((495631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330731/10000000) (δ := 8263/1000000000) (ψ := -250289/1000000) 164 120
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t99 : ((249051183711/2500000000000 : ℚ) : ℝ) ≤ stT164 99 := by
  have hc : ((247803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249051183711/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((247803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c100 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((13703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 947473/2500000) (δ := 8263/1000000000) (ψ := -250289/1000000) 164 120
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t100 : ((27380972619/5000000000000 : ℚ) : ℝ) ≤ stT164 100 := by
  have hc : ((27381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27380972619/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((27381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c101 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-999981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7838407/10000000) (δ := 837/100000000) (ψ := -250289/1000000) 164 121
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t101 : ((-497534423089/5000000000000 : ℚ) : ℝ) ≤ stT164 101 := by
  have hc : ((-1000031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497534423089/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-1000031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c102 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((12797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -949741/2500000) (δ := 837/100000000) (ψ := -250289/1000000) 164 121
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t102 : ((25317068643/5000000000000 : ℚ) : ℝ) ≤ stT164 102 := by
  have hc : ((25569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25317068643/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((25569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c103 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((31149/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 201037/10000000) (δ := 837/100000000) (ψ := -250289/1000000) 164 121
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t103 : ((491047575111/5000000000000 : ℚ) : ℝ) ≤ stT164 103 := by
  have hc : ((498359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((491047575111/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((498359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c104 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-94031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260151/625000) (δ := 837/100000000) (ψ := -250289/1000000) 164 121
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t104 : ((-92254041061/10000000000000 : ℚ) : ℝ) ≤ stT164 104 := by
  have hc : ((-94081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92254041061/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-94081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c105 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-9957/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7622053/10000000) (δ := 4163/500000000) (ψ := -250289/1000000) 164 122
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t105 : ((-3887013683/40000000000 : ℚ) : ℝ) ≤ stT164 105 := by
  have hc : ((-3983/4000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3887013683/40000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-3983/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c106 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((76407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1867893/5000000) (δ := 4163/500000000) (ψ := -250289/1000000) 164 122
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t106 : ((14832881749/2000000000000 : ℚ) : ℝ) ≤ stT164 106 := by
  have hc : ((76357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14832881749/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((76357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c107 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((12487/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7127/625000) (δ := 4163/500000000) (ψ := -250289/1000000) 164 122
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t107 : ((6035514111/62500000000 : ℚ) : ℝ) ≤ stT164 107 := by
  have hc : ((99891/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6035514111/62500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((99891/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c108 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-41/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245501/625000) (δ := 4163/500000000) (ψ := -250289/1000000) 164 122
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t108 : ((-22131773/500000000000 : ℚ) : ℝ) ≤ stT164 108 := by
  have hc : ((-23/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22131773/500000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-23/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c109 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-249567/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3853411/5000000) (δ := 4163/500000000) (ψ := -250289/1000000) 164 122
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t109 : ((-478107967493/5000000000000 : ℚ) : ℝ) ≤ stT164 109 := by
  have hc : ((-499159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478107967493/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-499159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c110 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-32887/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266051/625000) (δ := 4109/500000000) (ψ := -250289/1000000) 164 123
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t110 : ((-62736911937/5000000000000 : ℚ) : ℝ) ≤ stT164 110 := by
  have hc : ((-65799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62736911937/5000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-65799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c111 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((488107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -546357/10000000) (δ := 4109/500000000) (ψ := -250289/1000000) 164 123
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t111 : ((231633223437/2500000000000 : ℚ) : ℝ) ≤ stT164 111 := by
  have hc : ((244041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231633223437/2500000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((244041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c112 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((78283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3130769/10000000) (δ := 4109/500000000) (ψ := -250289/1000000) 164 123
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t112 : ((147917312851/5000000000000 : ℚ) : ℝ) ≤ stT164 112 := by
  have hc : ((156541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147917312851/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((156541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c113 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-113543/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6775259/10000000) (δ := 4109/500000000) (ψ := -250289/1000000) 164 123
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t113 : ((-427272656037/5000000000000 : ℚ) : ℝ) ≤ stT164 113 := by
  have hc : ((-454197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427272656037/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-454197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c114 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-66117/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2660179/5000000) (δ := 2073/250000000) (ψ := -250289/1000000) 164 124
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t114 : ((-123860220449/2500000000000 : ℚ) : ℝ) ≤ stT164 114 := by
  have hc : ((-264493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123860220449/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-264493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c115 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((767531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1739541/10000000) (δ := 2073/250000000) (ψ := -250289/1000000) 164 124
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t115 : ((89459887803/1250000000000 : ℚ) : ℝ) ≤ stT164 115 := by
  have hc : ((767481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89459887803/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((767481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c116 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((749099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1810239/10000000) (δ := 2073/250000000) (ψ := -250289/1000000) 164 124
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t116 : ((173868504831/2500000000000 : ℚ) : ℝ) ≤ stT164 116 := by
  have hc : ((749049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173868504831/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((749049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c117 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-532069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5329597/10000000) (δ := 2073/250000000) (ψ := -250289/1000000) 164 124
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t117 : ((-491944547619/10000000000000 : ℚ) : ℝ) ≤ stT164 117 := by
  have hc : ((-532119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-491944547619/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-532119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c118 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-463211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6888979/10000000) (δ := 8399/1000000000) (ψ := -250289/1000000) 164 125
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t118 : ((-4264434807/50000000000 : ℚ) : ℝ) ≤ stT164 118 := by
  have hc : ((-115809/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4264434807/50000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-115809/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c119 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((98927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3429071/10000000) (δ := 8399/1000000000) (ψ := -250289/1000000) 164 125
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t119 : ((22665816399/1250000000000 : ℚ) : ℝ) ≤ stT164 119 := by
  have hc : ((49451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22665816399/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((49451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c120 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 483/2500000) (δ := 8399/1000000000) (ψ := -250289/1000000) 164 125
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t120 : ((1825648713/20000000000 : ℚ) : ℝ) ≤ stT164 120 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1825648713/20000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c121 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((103751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85111/250000) (δ := 8399/1000000000) (ψ := -250289/1000000) 164 125
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t121 : ((4714813467/250000000000 : ℚ) : ℝ) ≤ stT164 121 := by
  have hc : ((51863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4714813467/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((51863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c122 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-5681/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1355789/2000000) (δ := 8399/1000000000) (ψ := -250289/1000000) 164 125
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t122 : ((-41148973779/500000000000 : ℚ) : ℝ) ≤ stT164 122 := by
  have hc : ((-90901/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41148973779/500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-90901/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c123 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-614719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2791033/5000000) (δ := 8297/1000000000) (ψ := -250289/1000000) 164 126
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t123 : ((-55431876423/1000000000000 : ℚ) : ℝ) ≤ stT164 123 := by
  have hc : ((-614769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55431876423/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-614769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c124 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((38611/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1131107/5000000) (δ := 8297/1000000000) (ψ := -250289/1000000) 164 126
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t124 : ((138683502219/2500000000000 : ℚ) : ℝ) ≤ stT164 124 := by
  have hc : ((308863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138683502219/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((308863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c125 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((916163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 257747/2500000) (δ := 8297/1000000000) (ψ := -250289/1000000) 164 126
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t125 : ((819396202251/10000000000000 : ℚ) : ℝ) ≤ stT164 125 := by
  have hc : ((916113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((819396202251/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((916113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c126 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-462/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85959/200000) (δ := 8297/1000000000) (ψ := -250289/1000000) 164 126
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t126 : ((-13175091219/1000000000000 : ℚ) : ℝ) ≤ stT164 126 := by
  have hc : ((-14789/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13175091219/1000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-14789/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c127 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-39683/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7539041/10000000) (δ := 8297/1000000000) (ψ := -250289/1000000) 164 126
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t127 : ((-7042952509/80000000000 : ℚ) : ℝ) ≤ stT164 127 := by
  have hc : ((-7937/8000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7042952509/80000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-7937/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c128 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-399057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495321/1000000) (δ := 8213/1000000000) (ψ := -250289/1000000) 164 127
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t128 : ((-88191072897/2500000000000 : ℚ) : ℝ) ≤ stT164 128 := by
  have hc : ((-399107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88191072897/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-399107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c129 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((761609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -440627/2500000) (δ := 8213/1000000000) (ψ := -250289/1000000) 164 127
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t129 : ((13410292431/200000000000 : ℚ) : ℝ) ≤ stT164 129 := by
  have hc : ((761559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13410292431/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((761559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c130 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((211627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175439/1250000) (δ := 8213/1000000000) (ψ := -250289/1000000) 164 127
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t130 : ((185598190141/2500000000000 : ℚ) : ℝ) ≤ stT164 130 := by
  have hc : ((423229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185598190141/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((423229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c131 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-24481/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4545301/10000000) (δ := 8213/1000000000) (ψ := -250289/1000000) 164 127
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t131 : ((-2139354063/100000000000 : ℚ) : ℝ) ≤ stT164 131 := by
  have hc : ((-12243/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2139354063/100000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-12243/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c132 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-997089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7663187/10000000) (δ := 8213/1000000000) (ψ := -250289/1000000) 164 127
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t132 : ((-867898817071/10000000000000 : ℚ) : ℝ) ≤ stT164 132 := by
  have hc : ((-997139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-867898817071/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-997139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c133 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-199017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618803/1250000) (δ := 13/1562500) (ψ := -250289/1000000) 164 128
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t133 : ((-8629565431/250000000000 : ℚ) : ℝ) ≤ stT164 133 := by
  have hc : ((-99521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8629565431/250000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-99521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c134 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((730527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -939629/5000000) (δ := 16483/1000000000) (ψ := -250289/1000000) 164 128
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t134 : ((157758926259/2500000000000 : ℚ) : ℝ) ≤ stT164 134 := by
  have hc : ((730477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157758926259/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((730477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c135 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((5579/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73067/625000) (δ := 13/1562500) (ψ := -250289/1000000) 164 128
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t135 : ((38410914729/500000000000 : ℚ) : ℝ) ≤ stT164 135 := by
  have hc : ((89259/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38410914729/500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((89259/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c136 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-26741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4194913/10000000) (δ := 13/1562500) (ψ := -250289/1000000) 164 128
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t136 : ((-45881877951/5000000000000 : ℚ) : ℝ) ≤ stT164 136 := by
  have hc : ((-53507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45881877951/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-53507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c137 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-241459/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3599307/5000000) (δ := 13/1562500) (ψ := -250289/1000000) 164 128
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t137 : ((-206303107797/2500000000000 : ℚ) : ℝ) ≤ stT164 137 := by
  have hc : ((-482943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206303107797/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-482943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c138 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-597373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5527543/10000000) (δ := 67/8000000) (ψ := -250289/1000000) 164 129
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t138 : ((-508560510711/10000000000000 : ℚ) : ℝ) ≤ stT164 138 := by
  have hc : ((-597423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508560510711/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-597423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c139 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((129371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128361/500000) (δ := 67/8000000) (ψ := -250289/1000000) 164 129
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t139 : ((54860163699/1250000000000 : ℚ) : ℝ) ≤ stT164 139 := by
  have hc : ((258717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54860163699/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((258717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c140 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((494479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74373/2000000) (δ := 67/8000000) (ψ := -250289/1000000) 164 129
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t140 : ((104472443979/1250000000000 : ℚ) : ℝ) ≤ stT164 140 := by
  have hc : ((247227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104472443979/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((247227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c141 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((252049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3289999/10000000) (δ := 67/8000000) (ψ := -250289/1000000) 164 129
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t141 : ((212221209849/10000000000000 : ℚ) : ℝ) ≤ stT164 141 := by
  have hc : ((251999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212221209849/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((251999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c142 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-392973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6187551/10000000) (δ := 67/8000000) (ψ := -250289/1000000) 164 129
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t142 : ((-82449211909/1250000000000 : ℚ) : ℝ) ≤ stT164 142 := by
  have hc : ((-196499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82449211909/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-196499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c143 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-442497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1660799/2500000) (δ := 2067/250000000) (ψ := -250289/1000000) 164 130
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t143 : ((-185027962423/2500000000000 : ℚ) : ℝ) ≤ stT164 143 := by
  have hc : ((-221261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185027962423/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-221261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c144 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((28169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378607/1000000) (δ := 2067/250000000) (ψ := -250289/1000000) 164 130
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t144 : ((1465832747/312500000000 : ℚ) : ℝ) ≤ stT164 144 := by
  have hc : ((1759/31250 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1465832747/312500000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((1759/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c145 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((928863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189733/2000000) (δ := 2067/250000000) (ψ := -250289/1000000) 164 130
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t145 : ((385668235551/5000000000000 : ℚ) : ℝ) ≤ stT164 145 := by
  have hc : ((928813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((385668235551/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((928813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c146 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((366631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233653/1250000) (δ := 2067/250000000) (ψ := -250289/1000000) 164 130
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t146 : ((30340495863/500000000000 : ℚ) : ℝ) ≤ stT164 146 := by
  have hc : ((183303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30340495863/500000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((183303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c147 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-292023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4667843/10000000) (δ := 2067/250000000) (ψ := -250289/1000000) 164 130
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t147 : ((-240898013451/10000000000000 : ℚ) : ℝ) ≤ stT164 147 := by
  have hc : ((-292073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240898013451/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-292073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c148 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-246703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46547/62500) (δ := 2067/250000000) (ψ := -250289/1000000) 164 130
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t148 : ((-81119562969/1000000000000 : ℚ) : ℝ) ≤ stT164 148 := by
  have hc : ((-493431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81119562969/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-493431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c149 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-588327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2749731/5000000) (δ := 4121/500000000) (ψ := -250289/1000000) 164 131
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t149 : ((-15063039577/312500000000 : ℚ) : ℝ) ≤ stT164 149 := by
  have hc : ((-588377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15063039577/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-588377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c150 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((225547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2757013/10000000) (δ := 4121/500000000) (ψ := -250289/1000000) 164 131
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t150 : ((5754306591/156250000000 : ℚ) : ℝ) ≤ stT164 150 := by
  have hc : ((112761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5754306591/156250000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((112761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c151 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((499957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32727/10000000) (δ := 4121/500000000) (ψ := -250289/1000000) 164 131
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t151 : ((25427416401/312500000000 : ℚ) : ℝ) ≤ stT164 151 := by
  have hc : ((124983/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25427416401/312500000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((124983/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c152 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((480629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66839/250000) (δ := 4121/500000000) (ψ := -250289/1000000) 164 131
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t152 : ((389800990953/10000000000000 : ℚ) : ℝ) ≤ stT164 152 := by
  have hc : ((480579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389800990953/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((480579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c153 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-54303/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2681047/5000000) (δ := 4121/500000000) (ψ := -250289/1000000) 164 131
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t153 : ((-10976366381/250000000000 : ℚ) : ℝ) ≤ stT164 153 := by
  have hc : ((-13577/25000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10976366381/250000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-13577/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c154 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-498717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3837421/5000000) (δ := 8349/1000000000) (ψ := -250289/1000000) 164 132
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t154 : ((-200948887333/2500000000000 : ℚ) : ℝ) ≤ stT164 154 := by
  have hc : ((-249371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200948887333/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-249371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c155 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-423813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5021117/10000000) (δ := 8349/1000000000) (ψ := -250289/1000000) 164 132
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t155 : ((-17022761943/500000000000 : ℚ) : ℝ) ≤ stT164 155 := by
  have hc : ((-423863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17022761943/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-423863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c156 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((115721/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37257/156250) (δ := 8349/1000000000) (ψ := -250289/1000000) 164 132
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t156 : ((144754461/3125000000 : ℚ) : ℝ) ≤ stT164 156 := by
  have hc : ((115711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144754461/3125000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((115711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c157 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((995571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23537/1000000) (δ := 8349/1000000000) (ψ := -250289/1000000) 164 132
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t157 : ((397255686403/5000000000000 : ℚ) : ℝ) ≤ stT164 157 := by
  have hc : ((995521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397255686403/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((995521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c158 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((84351/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1419271/5000000) (δ := 8349/1000000000) (ψ := -250289/1000000) 164 132
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t158 : ((67098072937/2000000000000 : ℚ) : ℝ) ≤ stT164 158 := by
  have hc : ((84341/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67098072937/2000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((84341/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c159 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-564089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2712657/5000000) (δ := 8349/1000000000) (ψ := -250289/1000000) 164 132
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t159 : ((-111847890557/2500000000000 : ℚ) : ℝ) ≤ stT164 159 := by
  have hc : ((-564139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111847890557/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-564139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c160 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-99839/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3856057/5000000) (δ := 8347/1000000000) (ψ := -250289/1000000) 164 133
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t160 : ((-1973341777/25000000000 : ℚ) : ℝ) ≤ stT164 160 := by
  have hc : ((-24961/25000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1973341777/25000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-24961/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c161 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-14769/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5157609/10000000) (δ := 8347/1000000000) (ψ := -250289/1000000) 164 133
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t161 : ((-186253484519/5000000000000 : ℚ) : ℝ) ≤ stT164 161 := by
  have hc : ((-236329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186253484519/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-236329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c162 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((49969/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2618889/10000000) (δ := 8347/1000000000) (ψ := -250289/1000000) 164 133
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t162 : ((4906926967/125000000000 : ℚ) : ℝ) ≤ stT164 162 := by
  have hc : ((12491/25000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4906926967/125000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((12491/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c163 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((499633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9579/1000000) (δ := 8347/1000000000) (ψ := -250289/1000000) 164 133
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t163 : ((2445768513/31250000000 : ℚ) : ℝ) ≤ stT164 163 := by
  have hc : ((62451/62500 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2445768513/31250000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((62451/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c164 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((56963/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 602963/2500000) (δ := 8347/1000000000) (ψ := -250289/1000000) 164 133
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t164 : ((5559584943/125000000000 : ℚ) : ℝ) ≤ stT164 164 := by
  have hc : ((28479/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5559584943/125000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((28479/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c165 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-381021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2452121/5000000) (δ := 8347/1000000000) (ψ := -250289/1000000) 164 133
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t165 : ((-296663392429/10000000000000 : ℚ) : ℝ) ≤ stT164 165 := by
  have hc : ((-381071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296663392429/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-381071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c166 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-4911/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1476317/2000000) (δ := 8347/1000000000) (ψ := -250289/1000000) 164 133
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t166 : ((-3049497279/40000000000 : ℚ) : ℝ) ≤ stT164 166 := by
  have hc : ((-3929/4000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3049497279/40000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-3929/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c167 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-699541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5863877/10000000) (δ := 8239/1000000000) (ψ := -250289/1000000) 164 134
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t167 : ((-8458754781/156250000000 : ℚ) : ℝ) ≤ stT164 167 := by
  have hc : ((-699591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8458754781/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-699591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c168 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((202923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -427017/1250000) (δ := 8239/1000000000) (ψ := -250289/1000000) 164 134
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t168 : ((39129941367/2500000000000 : ℚ) : ℝ) ≤ stT164 168 := by
  have hc : ((202873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39129941367/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((202873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c169 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((230927/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245717/2500000) (δ := 8239/1000000000) (ψ := -250289/1000000) 164 134
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t169 : ((35525272167/500000000000 : ℚ) : ℝ) ≤ stT164 169 := by
  have hc : ((461829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35525272167/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((461829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c170 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((209879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1436009/10000000) (δ := 8239/1000000000) (ψ := -250289/1000000) 164 134
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t170 : ((80480025153/1250000000000 : ℚ) : ℝ) ≤ stT164 170 := by
  have hc : ((419733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80480025153/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((419733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c171 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((34509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38407/100000) (δ := 8239/1000000000) (ψ := -250289/1000000) 164 134
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t171 : ((26351452021/10000000000000 : ℚ) : ℝ) ≤ stT164 171 := by
  have hc : ((34459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26351452021/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((34459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c172 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-796661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6231369/10000000) (δ := 8239/1000000000) (ψ := -250289/1000000) 164 134
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t172 : ((-607486560523/10000000000000 : ℚ) : ℝ) ≤ stT164 172 := by
  have hc : ((-796711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-607486560523/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-796711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c173 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-954839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7099783/10000000) (δ := 8271/1000000000) (ψ := -250289/1000000) 164 135
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t173 : ((-362994369127/5000000000000 : ℚ) : ℝ) ≤ stT164 173 := by
  have hc : ((-954889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362994369127/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-954889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c174 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-159119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2368333/5000000) (δ := 8271/1000000000) (ψ := -250289/1000000) 164 135
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t174 : ((-15080863407/625000000000 : ℚ) : ℝ) ≤ stT164 174 := by
  have hc : ((-19893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15080863407/625000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-19893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c175 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((288873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2387079/10000000) (δ := 8271/1000000000) (ψ := -250289/1000000) 164 135
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t175 : ((1705846023/39062500000 : ℚ) : ℝ) ≤ stT164 175 := by
  have hc : ((18053/31250 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1705846023/39062500000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((18053/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c176 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((999793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50899/10000000) (δ := 8271/1000000000) (ψ := -250289/1000000) 164 135
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t176 : ((376792139527/5000000000000 : ℚ) : ℝ) ≤ stT164 176 := by
  have hc : ((999743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376792139527/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((999743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c177 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((153667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2272079/10000000) (δ := 8271/1000000000) (ψ := -250289/1000000) 164 135
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t177 : ((115493790307/2500000000000 : ℚ) : ℝ) ≤ stT164 177 := by
  have hc : ((307309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115493790307/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((307309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c178 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-16187/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4581937/10000000) (δ := 8271/1000000000) (ψ := -250289/1000000) 164 135
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t178 : ((-24270033543/1250000000000 : ℚ) : ℝ) ≤ stT164 178 := by
  have hc : ((-129521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24270033543/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-129521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c179 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-462447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42993/62500) (δ := 8271/1000000000) (ψ := -250289/1000000) 164 135
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t179 : ((-10802131931/156250000000 : ℚ) : ℝ) ≤ stT164 179 := by
  have hc : ((-57809/62500 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10802131931/156250000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-57809/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c180 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-866023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6544973/10000000) (δ := 4189/500000000) (ψ := -250289/1000000) 164 136
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t180 : ((-161383176747/2500000000000 : ℚ) : ℝ) ≤ stT164 180 := by
  have hc : ((-866073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161383176747/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-866073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c181 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-138157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4273491/10000000) (δ := 4189/500000000) (ψ := -250289/1000000) 164 136
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t181 : ((-20545714413/2000000000000 : ℚ) : ℝ) ≤ stT164 181 := by
  have hc : ((-138207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20545714413/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-138207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c182 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((346259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402911/2000000) (δ := 4189/500000000) (ψ := -250289/1000000) 164 136
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t182 : ((128322803133/2500000000000 : ℚ) : ℝ) ≤ stT164 182 := by
  have hc : ((173117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128322803133/2500000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((173117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c183 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((62231/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5801/250000) (δ := 4189/500000000) (ψ := -250289/1000000) 164 136
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t183 : ((368001215883/5000000000000 : ℚ) : ℝ) ≤ stT164 183 := by
  have hc : ((497823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368001215883/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((497823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c184 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((551571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 308297/1250000) (δ := 4189/500000000) (ψ := -250289/1000000) 164 136
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t184 : ((406586244889/10000000000000 : ℚ) : ℝ) ≤ stT164 184 := by
  have hc : ((551521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((406586244889/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((551521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c185 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-7499/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4688617/10000000) (δ := 4189/500000000) (ψ := -250289/1000000) 164 136
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t185 : ((-4411437043/200000000000 : ℚ) : ℝ) ≤ stT164 185 := by
  have hc : ((-30001/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4411437043/200000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-30001/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c186 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-927901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1379769/2000000) (δ := 4189/500000000) (ψ := -250289/1000000) 164 136
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t186 : ((-170101769859/2500000000000 : ℚ) : ℝ) ≤ stT164 186 := by
  have hc : ((-927951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170101769859/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-927951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c187 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-219717/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6610699/10000000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 137
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t187 : ((-321364501307/5000000000000 : ℚ) : ℝ) ≤ stT164 187 := by
  have hc : ((-439459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321364501307/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-439459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c188 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-39503/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2212023/5000000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 137
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t188 : ((-1152712749/80000000000 : ℚ) : ℝ) ≤ stT164 188 := by
  have hc : ((-39513/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1152712749/80000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-39513/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c189 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((621937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449791/2000000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 137
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t189 : ((14136113397/312500000000 : ℚ) : ℝ) ≤ stT164 189 := by
  have hc : ((621887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14136113397/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((621887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c190 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((999417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17077/2000000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 137
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t190 : ((181254193423/2500000000000 : ℚ) : ℝ) ≤ stT164 190 := by
  have hc : ((999367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181254193423/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((999367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c191 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((84659/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2066869/10000000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 137
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t191 : ((122505057857/2500000000000 : ℚ) : ℝ) ≤ stT164 191 := by
  have hc : ((338611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122505057857/2500000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((338611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c192 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-112107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 525981/1250000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 137
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t192 : ((-10117795127/1250000000000 : ℚ) : ℝ) ≤ stT164 192 := by
  have hc : ((-112157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10117795127/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-112157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c193 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-205411/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1584429/2500000) (δ := 4159/500000000) (ψ := -250289/1000000) 164 137
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t193 : ((-36966780519/625000000000 : ℚ) : ℝ) ≤ stT164 193 := by
  have hc : ((-410847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36966780519/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-410847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c194 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-971089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7251367/10000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t194 : ((-697237985301/10000000000000 : ℚ) : ℝ) ≤ stT164 194 := by
  have hc : ((-971139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-697237985301/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-971139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c195 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-467589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5143393/10000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t195 : ((-66976660497/2000000000000 : ℚ) : ℝ) ≤ stT164 195 := by
  have hc : ((-467639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66976660497/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-467639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c196 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((21567/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1523101/5000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t196 : ((24644403927/1000000000000 : ℚ) : ℝ) ≤ stT164 196 := by
  have hc : ((172511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24644403927/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((172511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c197 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((927223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -959671/10000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t197 : ((66058294731/1000000000000 : ℚ) : ℝ) ≤ stT164 197 := by
  have hc : ((927173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66058294731/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((927173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c198 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((450979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 558141/5000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t198 : ((160239514113/2500000000000 : ℚ) : ℝ) ≤ stT164 198 := by
  have hc : ((225477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160239514113/2500000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((225477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c199 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((29369/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159089/500000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t199 : ((5203895421/250000000000 : ℚ) : ℝ) ≤ stT164 199 := by
  have hc : ((7341/25000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5203895421/250000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((7341/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c200 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-250159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1047381/2000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t200 : ((-22113357211/625000000000 : ℚ) : ℝ) ≤ stT164 200 := by
  have hc : ((-31273/62500 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22113357211/625000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-31273/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c201 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-38957/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7281821/10000000) (δ := 8211/1000000000) (ψ := -250289/1000000) 164 138
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t201 : ((-13739787407/200000000000 : ℚ) : ℝ) ≤ stT164 201 := by
  have hc : ((-38959/40000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13739787407/200000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-38959/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c202 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-416851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1278287/2000000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t202 : ((-36664139981/625000000000 : ℚ) : ℝ) ≤ stT164 202 := by
  have hc : ((-104219/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36664139981/625000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-104219/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c203 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-174991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1091683/2500000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t203 : ((-122854801383/10000000000000 : ℚ) : ℝ) ≤ stT164 203 := by
  have hc : ((-175041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122854801383/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-175041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c204 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((73643/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293999/1250000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t204 : ((10311206829/250000000000 : ℚ) : ℝ) ≤ stT164 204 := by
  have hc : ((294547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10311206829/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((294547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c205 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((495189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86773/2500000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t205 : ((8645934813/125000000000 : ℚ) : ℝ) ≤ stT164 205 := by
  have hc : ((123791/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8645934813/125000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((123791/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c206 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((79047/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32961/200000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t206 : ((27535584893/500000000000 : ℚ) : ℝ) ≤ stT164 206 := by
  have hc : ((39521/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27535584893/500000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((39521/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c207 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((366/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 908379/2500000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t207 : ((1017115867/125000000000 : ℚ) : ℝ) ≤ stT164 207 := by
  have hc : ((11707/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1017115867/125000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((11707/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c208 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-124663/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5609429/10000000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t208 : ((-675353641/15625000000 : ℚ) : ℝ) ≤ stT164 208 := by
  have hc : ((-124673/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-675353641/15625000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-124673/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c209 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-993819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7575871/10000000) (δ := 8299/1000000000) (ψ := -250289/1000000) 164 139
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t209 : ((-137494819067/2000000000000 : ℚ) : ℝ) ≤ stT164 209 := by
  have hc : ((-993869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137494819067/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-993869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c210 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-391421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19297/31250) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t210 : ((-67530893859/1250000000000 : ℚ) : ℝ) ≤ stT164 210 := by
  have hc : ((-195723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67530893859/1250000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-195723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c211 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-119833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2113647/5000000) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t211 : ((-82530933807/10000000000000 : ℚ) : ℝ) ≤ stT164 211 := by
  have hc : ((-119883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82530933807/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-119883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c212 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((609387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2288773/10000000) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t212 : ((209246935137/5000000000000 : ℚ) : ℝ) ≤ stT164 212 := by
  have hc : ((609337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209246935137/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((609337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c213 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((989687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179677/5000000) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t213 : ((169521849189/2500000000000 : ℚ) : ℝ) ≤ stT164 213 := by
  have hc : ((989637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169521849189/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((989637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c214 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((101413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312209/2000000) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t214 : ((55456106559/1000000000000 : ℚ) : ℝ) ≤ stT164 214 := by
  have hc : ((405627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55456106559/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((405627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c215 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((18081/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694493/2000000) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t215 : ((1540965443/125000000000 : ℚ) : ℝ) ≤ stT164 215 := by
  have hc : ((4519/25000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1540965443/125000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((4519/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c216 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-547367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5375029/10000000) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t216 : ((-186235095319/5000000000000 : ℚ) : ℝ) ≤ stT164 216 := by
  have hc : ((-547417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186235095319/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-547417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c217 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-121591/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3634389/5000000) (δ := 2099/250000000) (ψ := -250289/1000000) 164 140
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t217 : ((-66036548141/1000000000000 : ℚ) : ℝ) ≤ stT164 217 := by
  have hc : ((-486389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66036548141/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-486389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c218 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-108481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409633/625000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t218 : ((-146953791207/2500000000000 : ℚ) : ℝ) ≤ stT164 218 := by
  have hc : ((-433949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146953791207/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-433949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c219 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-36973/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4677681/10000000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t219 : ((-49976568873/2500000000000 : ℚ) : ℝ) ≤ stT164 219 := by
  have hc : ((-147917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49976568873/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-147917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c220 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((8643/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2809803/10000000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t220 : ((2913213879/100000000000 : ℚ) : ℝ) ≤ stT164 220 := by
  have hc : ((4321/10000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2913213879/100000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((4321/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c221 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((92861/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -950371/10000000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t221 : ((243990747/3906250000 : ℚ) : ℝ) ≤ stT164 221 := by
  have hc : ((11607/12500 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243990747/3906250000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((11607/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c222 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((93581/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180123/2000000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t222 : ((1962627933/31250000000 : ℚ) : ℝ) ≤ stT164 222 := by
  have hc : ((11697/12500 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1962627933/31250000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((11697/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c223 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((56997/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2743319/10000000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t223 : ((152655194987/5000000000000 : ℚ) : ℝ) ≤ stT164 223 := by
  have hc : ((227963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152655194987/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((227963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c224 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-128693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2288891/5000000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t224 : ((-21500861643/1250000000000 : ℚ) : ℝ) ≤ stT164 224 := by
  have hc : ((-64359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21500861643/1250000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-64359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c225 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-418243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3202043/5000000) (δ := 8289/1000000000) (ψ := -250289/1000000) 164 141
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t225 : ((-69711368189/1250000000000 : ℚ) : ℝ) ≤ stT164 225 := by
  have hc : ((-104567/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69711368189/1250000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-104567/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c226 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-98917/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -467857/625000) (δ := 8291/500000000) (ψ := -250289/1000000) 164 142
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t226 : ((-32901012051/500000000000 : ℚ) : ℝ) ≤ stT164 226 := by
  have hc : ((-49461/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32901012051/500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-49461/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c227 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-321887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5675541/10000000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t227 : ((-6676897509/156250000000 : ℚ) : ℝ) ≤ stT164 227 := by
  have hc : ((-40239/62500 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6676897509/156250000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-40239/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c228 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((21457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -774669/2000000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t228 : ((7088564131/5000000000000 : ℚ) : ℝ) ≤ stT164 228 := by
  have hc : ((21407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7088564131/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((21407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c229 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((84211/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2079021/10000000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t229 : ((111288028971/2500000000000 : ℚ) : ℝ) ≤ stT164 229 := by
  have hc : ((336819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111288028971/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((336819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c230 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((496581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18283/625000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t230 : ((4092738691/62500000000 : ℚ) : ℝ) ≤ stT164 230 := by
  have hc : ((124139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4092738691/62500000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((124139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c231 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((207109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185777/1250000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t231 : ((272518698543/5000000000000 : ℚ) : ℝ) ≤ stT164 231 := by
  have hc : ((414193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272518698543/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((414193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c232 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((264703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 814313/2500000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t232 : ((43438290849/2500000000000 : ℚ) : ℝ) ≤ stT164 232 := by
  have hc : ((264653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43438290849/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((264653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c233 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-423663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5020703/10000000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t233 : ((-138791853993/5000000000000 : ℚ) : ℝ) ≤ stT164 233 := by
  have hc : ((-423713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138791853993/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-423713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c234 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-90857/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677661/1000000) (δ := 8221/1000000000) (ψ := -250289/1000000) 164 142
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t234 : ((-29699198751/500000000000 : ℚ) : ℝ) ≤ stT164 234 := by
  have hc : ((-45431/50000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29699198751/500000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-45431/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c235 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-964193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7182949/10000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t235 : ((-629003671947/10000000000000 : ℚ) : ℝ) ≤ stT164 235 := by
  have hc : ((-964243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629003671947/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-964243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c236 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-71197/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2720983/5000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t236 : ((-37079519657/1000000000000 : ℚ) : ℝ) ≤ stT164 236 := by
  have hc : ((-284813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37079519657/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-284813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c237 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((4367/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3708363/10000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t237 : ((5670087801/1000000000000 : ℚ) : ℝ) ≤ stT164 237 := by
  have hc : ((8729/100000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5670087801/1000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((8729/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c238 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((701837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -991029/5000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t238 : ((454900438761/10000000000000 : ℚ) : ℝ) ≤ stT164 238 := by
  have hc : ((701787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454900438761/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((701787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c239 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((994473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262969/10000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t239 : ((321619269929/5000000000000 : ℚ) : ℝ) ≤ stT164 239 := by
  have hc : ((994423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321619269929/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((994423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c240 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((418347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289789/2000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t240 : ((135012798017/2500000000000 : ℚ) : ℝ) ≤ stT164 240 := by
  have hc : ((209161/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135012798017/2500000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((209161/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c241 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((152199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126149/400000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t241 : ((12252974393/625000000000 : ℚ) : ℝ) ≤ stT164 241 := by
  have hc : ((76087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12252974393/625000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((76087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c242 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-72283/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4851453/10000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t242 : ((-1858869909/80000000000 : ℚ) : ℝ) ≤ stT164 242 := by
  have hc : ((-72293/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1858869909/80000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-72293/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c243 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-432731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 654217/1000000) (δ := 1041/125000000) (ψ := -250289/1000000) 164 143
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t243 : ((-69403351689/1250000000000 : ℚ) : ℝ) ≤ stT164 243 := by
  have hc : ((-108189/125000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69403351689/1250000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-108189/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c244 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-988951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3741003/5000000) (δ := 523/62500000) (ψ := -250289/1000000) 164 144
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t244 : ((-126628721037/2000000000000 : ℚ) : ℝ) ≤ stT164 244 := by
  have hc : ((-989001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126628721037/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-989001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c245 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-170639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2902563/5000000) (δ := 3287/200000000) (ψ := -250289/1000000) 164 144
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t245 : ((-218050636731/5000000000000 : ℚ) : ℝ) ≤ stT164 245 := by
  have hc : ((-341303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218050636731/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-341303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c246 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((-83129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4135053/10000000) (δ := 523/62500000) (ψ := -250289/1000000) 164 144
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t246 : ((-53033017283/10000000000000 : ℚ) : ℝ) ≤ stT164 246 := by
  have hc : ((-83179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53033017283/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-83179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c247 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((549771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -494353/2000000) (δ := 523/62500000) (ψ := -250289/1000000) 164 144
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t247 : ((87444669191/2500000000000 : ℚ) : ℝ) ≤ stT164 247 := by
  have hc : ((549721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87444669191/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((549721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c248 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((189461/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -815201/10000000) (δ := 523/62500000) (ψ := -250289/1000000) 164 144
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t248 : ((24060277/400000000 : ℚ) : ℝ) ≤ stT164 248 := by
  have hc : ((189451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24060277/400000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((189451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c249 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((944781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20867/250000) (δ := 523/62500000) (ψ := -250289/1000000) 164 144
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t249 : ((149674677061/2500000000000 : ℚ) : ℝ) ≤ stT164 249 := by
  have hc : ((944731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149674677061/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((944731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_c250 :
    |Real.cos (((164 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((273843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2478001/10000000) (δ := 523/62500000) (ψ := -250289/1000000) 164 144
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st164_t250 : ((17317756319/500000000000 : ℚ) : ℝ) ≤ stT164 250 := by
  have hc : ((136909/250000 : ℚ) : ℝ)
      ≤ Real.cos (((164 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st164_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17317756319/500000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((136909/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st164_p1 : ((968791/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT164 (i+1) := by
  rw [Finset.sum_range_one]
  exact st164_t1

theorem st164_p2 : ((28928831517/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT164 (i+1))
      = (∑ i ∈ Finset.range 1, stT164 (i+1)) + stT164 2 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 1
    simpa using h
  have hprev := st164_p1
  have hstep := st164_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p3 : ((6605245867971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT164 (i+1))
      = (∑ i ∈ Finset.range 2, stT164 (i+1)) + stT164 3 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 2
    simpa using h
  have hprev := st164_p2
  have hstep := st164_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p4 : ((7010585867971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT164 (i+1))
      = (∑ i ∈ Finset.range 3, stT164 (i+1)) + stT164 4 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 3
    simpa using h
  have hprev := st164_p3
  have hstep := st164_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p5 : ((2285947447709/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT164 (i+1))
      = (∑ i ∈ Finset.range 4, stT164 (i+1)) + stT164 5 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 4
    simpa using h
  have hprev := st164_p4
  have hstep := st164_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p6 : ((9862623015191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT164 (i+1))
      = (∑ i ∈ Finset.range 5, stT164 (i+1)) + stT164 6 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 5
    simpa using h
  have hprev := st164_p5
  have hstep := st164_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p7 : ((10781630225037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT164 (i+1))
      = (∑ i ∈ Finset.range 6, stT164 (i+1)) + stT164 7 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 6
    simpa using h
  have hprev := st164_p6
  have hstep := st164_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p8 : ((10067339219949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT164 (i+1))
      = (∑ i ∈ Finset.range 7, stT164 (i+1)) + stT164 8 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 7
    simpa using h
  have hprev := st164_p7
  have hstep := st164_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p9 : ((1755953792487/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT164 (i+1))
      = (∑ i ∈ Finset.range 8, stT164 (i+1)) + stT164 9 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 8
    simpa using h
  have hprev := st164_p8
  have hstep := st164_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p10 : ((4891654040777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT164 (i+1))
      = (∑ i ∈ Finset.range 9, stT164 (i+1)) + stT164 10 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 9
    simpa using h
  have hprev := st164_p9
  have hstep := st164_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p11 : ((4369722731807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT164 (i+1))
      = (∑ i ∈ Finset.range 10, stT164 (i+1)) + stT164 11 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 10
    simpa using h
  have hprev := st164_p10
  have hstep := st164_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p12 : ((19807803277237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT164 (i+1))
      = (∑ i ∈ Finset.range 11, stT164 (i+1)) + stT164 12 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 11
    simpa using h
  have hprev := st164_p11
  have hstep := st164_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p13 : ((22574092177237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT164 (i+1))
      = (∑ i ∈ Finset.range 12, stT164 (i+1)) + stT164 13 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 12
    simpa using h
  have hprev := st164_p12
  have hstep := st164_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p14 : ((24939482082613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT164 (i+1))
      = (∑ i ∈ Finset.range 13, stT164 (i+1)) + stT164 14 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 13
    simpa using h
  have hprev := st164_p13
  have hstep := st164_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p15 : ((12257843659049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT164 (i+1))
      = (∑ i ∈ Finset.range 14, stT164 (i+1)) + stT164 15 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 14
    simpa using h
  have hprev := st164_p14
  have hstep := st164_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p16 : ((22419063979449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT164 (i+1))
      = (∑ i ∈ Finset.range 15, stT164 (i+1)) + stT164 16 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 15
    simpa using h
  have hprev := st164_p15
  have hstep := st164_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p17 : ((24840158628957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT164 (i+1))
      = (∑ i ∈ Finset.range 16, stT164 (i+1)) + stT164 17 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 16
    simpa using h
  have hprev := st164_p16
  have hstep := st164_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p18 : ((22497065634887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT164 (i+1))
      = (∑ i ∈ Finset.range 17, stT164 (i+1)) + stT164 18 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 17
    simpa using h
  have hprev := st164_p17
  have hstep := st164_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p19 : ((24299437963739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT164 (i+1))
      = (∑ i ∈ Finset.range 18, stT164 (i+1)) + stT164 19 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 18
    simpa using h
  have hprev := st164_p18
  have hstep := st164_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p20 : ((3067786311551/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT164 (i+1))
      = (∑ i ∈ Finset.range 19, stT164 (i+1)) + stT164 20 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 19
    simpa using h
  have hprev := st164_p19
  have hstep := st164_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p21 : ((5590409754427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT164 (i+1))
      = (∑ i ∈ Finset.range 20, stT164 (i+1)) + stT164 21 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 20
    simpa using h
  have hprev := st164_p20
  have hstep := st164_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p22 : ((5491834765541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT164 (i+1))
      = (∑ i ∈ Finset.range 21, stT164 (i+1)) + stT164 22 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 21
    simpa using h
  have hprev := st164_p21
  have hstep := st164_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p23 : ((5873281625753/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT164 (i+1))
      = (∑ i ∈ Finset.range 22, stT164 (i+1)) + stT164 23 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 22
    simpa using h
  have hprev := st164_p22
  have hstep := st164_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p24 : ((3191421370153/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT164 (i+1))
      = (∑ i ∈ Finset.range 23, stT164 (i+1)) + stT164 24 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 23
    simpa using h
  have hprev := st164_p23
  have hstep := st164_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p25 : ((3425526870153/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT164 (i+1))
      = (∑ i ∈ Finset.range 24, stT164 (i+1)) + stT164 25 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 24
    simpa using h
  have hprev := st164_p24
  have hstep := st164_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p26 : ((14559109342519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT164 (i+1))
      = (∑ i ∈ Finset.range 25, stT164 (i+1)) + stT164 26 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 25
    simpa using h
  have hprev := st164_p25
  have hstep := st164_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p27 : ((15440175272269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT164 (i+1))
      = (∑ i ∈ Finset.range 26, stT164 (i+1)) + stT164 27 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 26
    simpa using h
  have hprev := st164_p26
  have hstep := st164_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p28 : ((16380803935617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT164 (i+1))
      = (∑ i ∈ Finset.range 27, stT164 (i+1)) + stT164 28 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 27
    simpa using h
  have hprev := st164_p27
  have hstep := st164_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p29 : ((3444670358499/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT164 (i+1))
      = (∑ i ∈ Finset.range 28, stT164 (i+1)) + stT164 29 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 28
    simpa using h
  have hprev := st164_p28
  have hstep := st164_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p30 : ((1099405970463/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT164 (i+1))
      = (∑ i ∈ Finset.range 29, stT164 (i+1)) + stT164 30 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 29
    simpa using h
  have hprev := st164_p29
  have hstep := st164_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p31 : ((1072905193693/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT164 (i+1))
      = (∑ i ∈ Finset.range 30, stT164 (i+1)) + stT164 31 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 30
    simpa using h
  have hprev := st164_p30
  have hstep := st164_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p32 : ((16282558940447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT164 (i+1))
      = (∑ i ∈ Finset.range 31, stT164 (i+1)) + stT164 32 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 31
    simpa using h
  have hprev := st164_p31
  have hstep := st164_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p33 : ((31989646597903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT164 (i+1))
      = (∑ i ∈ Finset.range 32, stT164 (i+1)) + stT164 33 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 32
    simpa using h
  have hprev := st164_p32
  have hstep := st164_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p34 : ((4184692732391/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT164 (i+1))
      = (∑ i ∈ Finset.range 33, stT164 (i+1)) + stT164 34 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 33
    simpa using h
  have hprev := st164_p33
  have hstep := st164_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p35 : ((4297261329113/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT164 (i+1))
      = (∑ i ∈ Finset.range 34, stT164 (i+1)) + stT164 35 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 34
    simpa using h
  have hprev := st164_p34
  have hstep := st164_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p36 : ((32891735335633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT164 (i+1))
      = (∑ i ∈ Finset.range 35, stT164 (i+1)) + stT164 36 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 35
    simpa using h
  have hprev := st164_p35
  have hstep := st164_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p37 : ((32483940328153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT164 (i+1))
      = (∑ i ∈ Finset.range 36, stT164 (i+1)) + stT164 37 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 36
    simpa using h
  have hprev := st164_p36
  have hstep := st164_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p38 : ((34099769293849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT164 (i+1))
      = (∑ i ∈ Finset.range 37, stT164 (i+1)) + stT164 38 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 37
    simpa using h
  have hprev := st164_p37
  have hstep := st164_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p39 : ((33275597454859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT164 (i+1))
      = (∑ i ∈ Finset.range 38, stT164 (i+1)) + stT164 39 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 38
    simpa using h
  have hprev := st164_p38
  have hstep := st164_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p40 : ((6511907509819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT164 (i+1))
      = (∑ i ∈ Finset.range 39, stT164 (i+1)) + stT164 40 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 39
    simpa using h
  have hprev := st164_p39
  have hstep := st164_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p41 : ((34092238734791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT164 (i+1))
      = (∑ i ∈ Finset.range 40, stT164 (i+1)) + stT164 41 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 40
    simpa using h
  have hprev := st164_p40
  have hstep := st164_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p42 : ((32834121333789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT164 (i+1))
      = (∑ i ∈ Finset.range 41, stT164 (i+1)) + stT164 42 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 41
    simpa using h
  have hprev := st164_p41
  have hstep := st164_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p43 : ((33190376129609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT164 (i+1))
      = (∑ i ∈ Finset.range 42, stT164 (i+1)) + stT164 43 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 42
    simpa using h
  have hprev := st164_p42
  have hstep := st164_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p44 : ((6753483461901/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT164 (i+1))
      = (∑ i ∈ Finset.range 43, stT164 (i+1)) + stT164 44 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 43
    simpa using h
  have hprev := st164_p43
  have hstep := st164_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p45 : ((6513267148797/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT164 (i+1))
      = (∑ i ∈ Finset.range 44, stT164 (i+1)) + stT164 45 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 44
    simpa using h
  have hprev := st164_p44
  have hstep := st164_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p46 : ((3401916187773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT164 (i+1))
      = (∑ i ∈ Finset.range 45, stT164 (i+1)) + stT164 46 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 45
    simpa using h
  have hprev := st164_p45
  have hstep := st164_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p47 : ((3259383036103/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT164 (i+1))
      = (∑ i ∈ Finset.range 46, stT164 (i+1)) + stT164 47 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 46
    simpa using h
  have hprev := st164_p46
  have hstep := st164_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p48 : ((6768470235881/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT164 (i+1))
      = (∑ i ∈ Finset.range 47, stT164 (i+1)) + stT164 48 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 47
    simpa using h
  have hprev := st164_p47
  have hstep := st164_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p49 : ((6562445867757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT164 (i+1))
      = (∑ i ∈ Finset.range 48, stT164 (i+1)) + stT164 49 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 48
    simpa using h
  have hprev := st164_p48
  have hstep := st164_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p50 : ((8412368990421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT164 (i+1))
      = (∑ i ∈ Finset.range 49, stT164 (i+1)) + stT164 50 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 49
    simpa using h
  have hprev := st164_p49
  have hstep := st164_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p51 : ((32944424676217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT164 (i+1))
      = (∑ i ∈ Finset.range 50, stT164 (i+1)) + stT164 51 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 50
    simpa using h
  have hprev := st164_p50
  have hstep := st164_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p52 : ((33590401947967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT164 (i+1))
      = (∑ i ∈ Finset.range 51, stT164 (i+1)) + stT164 52 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 51
    simpa using h
  have hprev := st164_p51
  have hstep := st164_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p53 : ((32929012032573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT164 (i+1))
      = (∑ i ∈ Finset.range 52, stT164 (i+1)) + stT164 53 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 52
    simpa using h
  have hprev := st164_p52
  have hstep := st164_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p54 : ((3367288225641/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT164 (i+1))
      = (∑ i ∈ Finset.range 53, stT164 (i+1)) + stT164 54 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 53
    simpa using h
  have hprev := st164_p53
  have hstep := st164_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p55 : ((3279313081201/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT164 (i+1))
      = (∑ i ∈ Finset.range 54, stT164 (i+1)) + stT164 55 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 54
    simpa using h
  have hprev := st164_p54
  have hstep := st164_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p56 : ((16918788445581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT164 (i+1))
      = (∑ i ∈ Finset.range 55, stT164 (i+1)) + stT164 56 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 55
    simpa using h
  have hprev := st164_p55
  have hstep := st164_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p57 : ((8159033185713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT164 (i+1))
      = (∑ i ∈ Finset.range 56, stT164 (i+1)) + stT164 57 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 56
    simpa using h
  have hprev := st164_p56
  have hstep := st164_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p58 : ((1696764701061/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT164 (i+1))
      = (∑ i ∈ Finset.range 57, stT164 (i+1)) + stT164 58 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 57
    simpa using h
  have hprev := st164_p57
  have hstep := st164_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p59 : ((3265746164653/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT164 (i+1))
      = (∑ i ∈ Finset.range 58, stT164 (i+1)) + stT164 59 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 58
    simpa using h
  have hprev := st164_p58
  have hstep := st164_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p60 : ((8434663730149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT164 (i+1))
      = (∑ i ∈ Finset.range 59, stT164 (i+1)) + stT164 60 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 59
    simpa using h
  have hprev := st164_p59
  have hstep := st164_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p61 : ((1322253390287/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT164 (i+1))
      = (∑ i ∈ Finset.range 60, stT164 (i+1)) + stT164 61 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 60
    simpa using h
  have hprev := st164_p60
  have hstep := st164_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p62 : ((829168874853/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT164 (i+1))
      = (∑ i ∈ Finset.range 61, stT164 (i+1)) + stT164 62 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 61
    simpa using h
  have hprev := st164_p61
  have hstep := st164_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p63 : ((8423095596711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT164 (i+1))
      = (∑ i ∈ Finset.range 62, stT164 (i+1)) + stT164 63 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 62
    simpa using h
  have hprev := st164_p62
  have hstep := st164_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p64 : ((8161942887789/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT164 (i+1))
      = (∑ i ∈ Finset.range 63, stT164 (i+1)) + stT164 64 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 63
    simpa using h
  have hprev := st164_p63
  have hstep := st164_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p65 : ((33887869241409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT164 (i+1))
      = (∑ i ∈ Finset.range 64, stT164 (i+1)) + stT164 65 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 64
    simpa using h
  have hprev := st164_p64
  have hstep := st164_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p66 : ((8227931333841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT164 (i+1))
      = (∑ i ∈ Finset.range 65, stT164 (i+1)) + stT164 66 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 65
    simpa using h
  have hprev := st164_p65
  have hstep := st164_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p67 : ((8300603801431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT164 (i+1))
      = (∑ i ∈ Finset.range 66, stT164 (i+1)) + stT164 67 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 66
    simpa using h
  have hprev := st164_p66
  have hstep := st164_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p68 : ((8438327641891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT164 (i+1))
      = (∑ i ∈ Finset.range 67, stT164 (i+1)) + stT164 68 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 67
    simpa using h
  have hprev := st164_p67
  have hstep := st164_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p69 : ((32623116903633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT164 (i+1))
      = (∑ i ∈ Finset.range 68, stT164 (i+1)) + stT164 69 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 68
    simpa using h
  have hprev := st164_p68
  have hstep := st164_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p70 : ((33709448875781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT164 (i+1))
      = (∑ i ∈ Finset.range 69, stT164 (i+1)) + stT164 70 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 69
    simpa using h
  have hprev := st164_p69
  have hstep := st164_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p71 : ((33329968210589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT164 (i+1))
      = (∑ i ∈ Finset.range 70, stT164 (i+1)) + stT164 71 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 70
    simpa using h
  have hprev := st164_p70
  have hstep := st164_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p72 : ((32741856545741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT164 (i+1))
      = (∑ i ∈ Finset.range 71, stT164 (i+1)) + stT164 72 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 71
    simpa using h
  have hprev := st164_p71
  have hstep := st164_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p73 : ((16947778793947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT164 (i+1))
      = (∑ i ∈ Finset.range 72, stT164 (i+1)) + stT164 73 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 72
    simpa using h
  have hprev := st164_p72
  have hstep := st164_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p74 : ((33038136639757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT164 (i+1))
      = (∑ i ∈ Finset.range 73, stT164 (i+1)) + stT164 74 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 73
    simpa using h
  have hprev := st164_p73
  have hstep := st164_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p75 : ((8227600615109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT164 (i+1))
      = (∑ i ∈ Finset.range 74, stT164 (i+1)) + stT164 75 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 74
    simpa using h
  have hprev := st164_p74
  have hstep := st164_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p76 : ((16961057466367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT164 (i+1))
      = (∑ i ∈ Finset.range 75, stT164 (i+1)) + stT164 76 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 75
    simpa using h
  have hprev := st164_p75
  have hstep := st164_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p77 : ((8231472685209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT164 (i+1))
      = (∑ i ∈ Finset.range 76, stT164 (i+1)) + stT164 77 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 76
    simpa using h
  have hprev := st164_p76
  have hstep := st164_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p78 : ((1648454468647/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT164 (i+1))
      = (∑ i ∈ Finset.range 77, stT164 (i+1)) + stT164 78 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 77
    simpa using h
  have hprev := st164_p77
  have hstep := st164_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p79 : ((1696214411797/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT164 (i+1))
      = (∑ i ∈ Finset.range 78, stT164 (i+1)) + stT164 79 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 78
    simpa using h
  have hprev := st164_p78
  have hstep := st164_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p80 : ((3295512605321/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT164 (i+1))
      = (∑ i ∈ Finset.range 79, stT164 (i+1)) + stT164 80 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 79
    simpa using h
  have hprev := st164_p79
  have hstep := st164_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p81 : ((16446681890789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT164 (i+1))
      = (∑ i ∈ Finset.range 80, stT164 (i+1)) + stT164 81 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 80
    simpa using h
  have hprev := st164_p80
  have hstep := st164_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p82 : ((33916397884633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT164 (i+1))
      = (∑ i ∈ Finset.range 81, stT164 (i+1)) + stT164 82 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 81
    simpa using h
  have hprev := st164_p81
  have hstep := st164_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p83 : ((8281653527443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT164 (i+1))
      = (∑ i ∈ Finset.range 82, stT164 (i+1)) + stT164 83 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 82
    simpa using h
  have hprev := st164_p82
  have hstep := st164_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p84 : ((8181868982583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT164 (i+1))
      = (∑ i ∈ Finset.range 83, stT164 (i+1)) + stT164 84 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 83
    simpa using h
  have hprev := st164_p83
  have hstep := st164_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p85 : ((8453015712803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT164 (i+1))
      = (∑ i ∈ Finset.range 84, stT164 (i+1)) + stT164 85 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 84
    simpa using h
  have hprev := st164_p84
  have hstep := st164_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p86 : ((8362351781637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT164 (i+1))
      = (∑ i ∈ Finset.range 85, stT164 (i+1)) + stT164 86 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 85
    simpa using h
  have hprev := st164_p85
  have hstep := st164_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p87 : ((32607769474497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT164 (i+1))
      = (∑ i ∈ Finset.range 86, stT164 (i+1)) + stT164 87 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 86
    simpa using h
  have hprev := st164_p86
  have hstep := st164_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p88 : ((6697607701559/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT164 (i+1))
      = (∑ i ∈ Finset.range 87, stT164 (i+1)) + stT164 88 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 87
    simpa using h
  have hprev := st164_p87
  have hstep := st164_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p89 : ((16909115376643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT164 (i+1))
      = (∑ i ∈ Finset.range 88, stT164 (i+1)) + stT164 89 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 88
    simpa using h
  have hprev := st164_p88
  have hstep := st164_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p90 : ((1310627617291/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT164 (i+1))
      = (∑ i ∈ Finset.range 89, stT164 (i+1)) + stT164 90 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 89
    simpa using h
  have hprev := st164_p89
  have hstep := st164_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p91 : ((32959678531327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT164 (i+1))
      = (∑ i ∈ Finset.range 90, stT164 (i+1)) + stT164 91 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 90
    simpa using h
  have hprev := st164_p90
  have hstep := st164_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p92 : ((33916725222451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT164 (i+1))
      = (∑ i ∈ Finset.range 91, stT164 (i+1)) + stT164 92 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 91
    simpa using h
  have hprev := st164_p91
  have hstep := st164_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p93 : ((33322691714971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT164 (i+1))
      = (∑ i ∈ Finset.range 92, stT164 (i+1)) + stT164 93 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 92
    simpa using h
  have hprev := st164_p92
  have hstep := st164_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p94 : ((32599003751469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT164 (i+1))
      = (∑ i ∈ Finset.range 93, stT164 (i+1)) + stT164 94 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 93
    simpa using h
  have hprev := st164_p93
  have hstep := st164_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p95 : ((33438150131691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT164 (i+1))
      = (∑ i ∈ Finset.range 94, stT164 (i+1)) + stT164 95 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 94
    simpa using h
  have hprev := st164_p94
  have hstep := st164_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p96 : ((33897101512671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT164 (i+1))
      = (∑ i ∈ Finset.range 95, stT164 (i+1)) + stT164 96 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 95
    simpa using h
  have hprev := st164_p95
  have hstep := st164_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p97 : ((4117383983271/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT164 (i+1))
      = (∑ i ∈ Finset.range 96, stT164 (i+1)) + stT164 97 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 96
    simpa using h
  have hprev := st164_p96
  have hstep := st164_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p98 : ((4089022927643/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT164 (i+1))
      = (∑ i ∈ Finset.range 97, stT164 (i+1)) + stT164 98 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 97
    simpa using h
  have hprev := st164_p97
  have hstep := st164_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p99 : ((8427097038997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT164 (i+1))
      = (∑ i ∈ Finset.range 98, stT164 (i+1)) + stT164 99 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 98
    simpa using h
  have hprev := st164_p98
  have hstep := st164_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p100 : ((16881575050613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT164 (i+1))
      = (∑ i ∈ Finset.range 99, stT164 (i+1)) + stT164 100 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 99
    simpa using h
  have hprev := st164_p99
  have hstep := st164_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p101 : ((4096010156881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT164 (i+1))
      = (∑ i ∈ Finset.range 100, stT164 (i+1)) + stT164 101 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 100
    simpa using h
  have hprev := st164_p100
  have hstep := st164_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p102 : ((16409357696167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT164 (i+1))
      = (∑ i ∈ Finset.range 101, stT164 (i+1)) + stT164 102 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 101
    simpa using h
  have hprev := st164_p101
  have hstep := st164_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p103 : ((8450202635639/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT164 (i+1))
      = (∑ i ∈ Finset.range 102, stT164 (i+1)) + stT164 103 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 102
    simpa using h
  have hprev := st164_p102
  have hstep := st164_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p104 : ((6741711300299/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT164 (i+1))
      = (∑ i ∈ Finset.range 103, stT164 (i+1)) + stT164 104 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 103
    simpa using h
  have hprev := st164_p103
  have hstep := st164_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p105 : ((6547360616149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT164 (i+1))
      = (∑ i ∈ Finset.range 104, stT164 (i+1)) + stT164 105 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 104
    simpa using h
  have hprev := st164_p104
  have hstep := st164_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p106 : ((3281096748949/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT164 (i+1))
      = (∑ i ∈ Finset.range 105, stT164 (i+1)) + stT164 106 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 105
    simpa using h
  have hprev := st164_p105
  have hstep := st164_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p107 : ((135106598989/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT164 (i+1))
      = (∑ i ∈ Finset.range 106, stT164 (i+1)) + stT164 107 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 106
    simpa using h
  have hprev := st164_p106
  have hstep := st164_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p108 : ((3377620711179/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT164 (i+1))
      = (∑ i ∈ Finset.range 107, stT164 (i+1)) + stT164 108 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 107
    simpa using h
  have hprev := st164_p107
  have hstep := st164_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p109 : ((8204997794201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT164 (i+1))
      = (∑ i ∈ Finset.range 108, stT164 (i+1)) + stT164 109 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 108
    simpa using h
  have hprev := st164_p108
  have hstep := st164_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p110 : ((3269451735293/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT164 (i+1))
      = (∑ i ∈ Finset.range 109, stT164 (i+1)) + stT164 110 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 109
    simpa using h
  have hprev := st164_p109
  have hstep := st164_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p111 : ((16810525123339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT164 (i+1))
      = (∑ i ∈ Finset.range 110, stT164 (i+1)) + stT164 111 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 110
    simpa using h
  have hprev := st164_p110
  have hstep := st164_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p112 : ((1695844243619/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT164 (i+1))
      = (∑ i ∈ Finset.range 111, stT164 (i+1)) + stT164 112 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 111
    simpa using h
  have hprev := st164_p111
  have hstep := st164_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p113 : ((16531169780153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT164 (i+1))
      = (∑ i ∈ Finset.range 112, stT164 (i+1)) + stT164 113 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 112
    simpa using h
  have hprev := st164_p112
  have hstep := st164_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p114 : ((3256689867851/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT164 (i+1))
      = (∑ i ∈ Finset.range 113, stT164 (i+1)) + stT164 114 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 113
    simpa using h
  have hprev := st164_p113
  have hstep := st164_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p115 : ((16641288890467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT164 (i+1))
      = (∑ i ∈ Finset.range 114, stT164 (i+1)) + stT164 115 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 114
    simpa using h
  have hprev := st164_p114
  have hstep := st164_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p116 : ((16989025900129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT164 (i+1))
      = (∑ i ∈ Finset.range 115, stT164 (i+1)) + stT164 116 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 115
    simpa using h
  have hprev := st164_p115
  have hstep := st164_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p117 : ((33486107252639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT164 (i+1))
      = (∑ i ∈ Finset.range 116, stT164 (i+1)) + stT164 117 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 116
    simpa using h
  have hprev := st164_p116
  have hstep := st164_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p118 : ((32633220291239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT164 (i+1))
      = (∑ i ∈ Finset.range 117, stT164 (i+1)) + stT164 118 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 117
    simpa using h
  have hprev := st164_p117
  have hstep := st164_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p119 : ((32814546822431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT164 (i+1))
      = (∑ i ∈ Finset.range 118, stT164 (i+1)) + stT164 119 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 118
    simpa using h
  have hprev := st164_p118
  have hstep := st164_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p120 : ((33727371178931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT164 (i+1))
      = (∑ i ∈ Finset.range 119, stT164 (i+1)) + stT164 120 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 119
    simpa using h
  have hprev := st164_p119
  have hstep := st164_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p121 : ((33915963717611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT164 (i+1))
      = (∑ i ∈ Finset.range 120, stT164 (i+1)) + stT164 121 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 120
    simpa using h
  have hprev := st164_p120
  have hstep := st164_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p122 : ((33092984242031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT164 (i+1))
      = (∑ i ∈ Finset.range 121, stT164 (i+1)) + stT164 122 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 121
    simpa using h
  have hprev := st164_p121
  have hstep := st164_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p123 : ((32538665477801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT164 (i+1))
      = (∑ i ∈ Finset.range 122, stT164 (i+1)) + stT164 123 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 122
    simpa using h
  have hprev := st164_p122
  have hstep := st164_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p124 : ((33093399486677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT164 (i+1))
      = (∑ i ∈ Finset.range 123, stT164 (i+1)) + stT164 124 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 123
    simpa using h
  have hprev := st164_p123
  have hstep := st164_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p125 : ((1059774865279/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT164 (i+1))
      = (∑ i ∈ Finset.range 124, stT164 (i+1)) + stT164 125 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 124
    simpa using h
  have hprev := st164_p124
  have hstep := st164_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p126 : ((16890522388369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT164 (i+1))
      = (∑ i ∈ Finset.range 125, stT164 (i+1)) + stT164 126 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 125
    simpa using h
  have hprev := st164_p125
  have hstep := st164_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p127 : ((32900675713113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT164 (i+1))
      = (∑ i ∈ Finset.range 126, stT164 (i+1)) + stT164 127 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 126
    simpa using h
  have hprev := st164_p126
  have hstep := st164_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p128 : ((1301916456861/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT164 (i+1))
      = (∑ i ∈ Finset.range 127, stT164 (i+1)) + stT164 128 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 127
    simpa using h
  have hprev := st164_p127
  have hstep := st164_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p129 : ((1328737041723/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT164 (i+1))
      = (∑ i ∈ Finset.range 128, stT164 (i+1)) + stT164 129 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 128
    simpa using h
  have hprev := st164_p128
  have hstep := st164_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p130 : ((33960818803639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT164 (i+1))
      = (∑ i ∈ Finset.range 129, stT164 (i+1)) + stT164 130 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 129
    simpa using h
  have hprev := st164_p129
  have hstep := st164_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p131 : ((33746883397339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT164 (i+1))
      = (∑ i ∈ Finset.range 130, stT164 (i+1)) + stT164 131 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 130
    simpa using h
  have hprev := st164_p130
  have hstep := st164_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p132 : ((8219746145067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT164 (i+1))
      = (∑ i ∈ Finset.range 131, stT164 (i+1)) + stT164 132 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 131
    simpa using h
  have hprev := st164_p131
  have hstep := st164_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p133 : ((8133450490757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT164 (i+1))
      = (∑ i ∈ Finset.range 132, stT164 (i+1)) + stT164 133 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 132
    simpa using h
  have hprev := st164_p132
  have hstep := st164_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p134 : ((1036401177127/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT164 (i+1))
      = (∑ i ∈ Finset.range 133, stT164 (i+1)) + stT164 134 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 133
    simpa using h
  have hprev := st164_p133
  have hstep := st164_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p135 : ((8483263990661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT164 (i+1))
      = (∑ i ∈ Finset.range 134, stT164 (i+1)) + stT164 135 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 134
    simpa using h
  have hprev := st164_p134
  have hstep := st164_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p136 : ((16920646103371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT164 (i+1))
      = (∑ i ∈ Finset.range 135, stT164 (i+1)) + stT164 136 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 135
    simpa using h
  have hprev := st164_p135
  have hstep := st164_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p137 : ((16508039887777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT164 (i+1))
      = (∑ i ∈ Finset.range 136, stT164 (i+1)) + stT164 137 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 136
    simpa using h
  have hprev := st164_p136
  have hstep := st164_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p138 : ((32507519264843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT164 (i+1))
      = (∑ i ∈ Finset.range 137, stT164 (i+1)) + stT164 138 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 137
    simpa using h
  have hprev := st164_p137
  have hstep := st164_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p139 : ((6589280114887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT164 (i+1))
      = (∑ i ∈ Finset.range 138, stT164 (i+1)) + stT164 139 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 138
    simpa using h
  have hprev := st164_p138
  have hstep := st164_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p140 : ((33782180126267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT164 (i+1))
      = (∑ i ∈ Finset.range 139, stT164 (i+1)) + stT164 140 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 139
    simpa using h
  have hprev := st164_p139
  have hstep := st164_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p141 : ((8498600334029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT164 (i+1))
      = (∑ i ∈ Finset.range 140, stT164 (i+1)) + stT164 141 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 140
    simpa using h
  have hprev := st164_p140
  have hstep := st164_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p142 : ((8333701910211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT164 (i+1))
      = (∑ i ∈ Finset.range 141, stT164 (i+1)) + stT164 142 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 141
    simpa using h
  have hprev := st164_p141
  have hstep := st164_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p143 : ((2037168486947/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT164 (i+1))
      = (∑ i ∈ Finset.range 142, stT164 (i+1)) + stT164 143 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 142
    simpa using h
  have hprev := st164_p142
  have hstep := st164_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p144 : ((2040100152441/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT164 (i+1))
      = (∑ i ∈ Finset.range 143, stT164 (i+1)) + stT164 144 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 143
    simpa using h
  have hprev := st164_p143
  have hstep := st164_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p145 : ((16706469455079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT164 (i+1))
      = (∑ i ∈ Finset.range 144, stT164 (i+1)) + stT164 145 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 144
    simpa using h
  have hprev := st164_p144
  have hstep := st164_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p146 : ((17009874413709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT164 (i+1))
      = (∑ i ∈ Finset.range 145, stT164 (i+1)) + stT164 146 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 145
    simpa using h
  have hprev := st164_p145
  have hstep := st164_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p147 : ((33778850813967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT164 (i+1))
      = (∑ i ∈ Finset.range 146, stT164 (i+1)) + stT164 147 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 146
    simpa using h
  have hprev := st164_p146
  have hstep := st164_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p148 : ((32967655184277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT164 (i+1))
      = (∑ i ∈ Finset.range 147, stT164 (i+1)) + stT164 148 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 147
    simpa using h
  have hprev := st164_p147
  have hstep := st164_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p149 : ((32485637917813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT164 (i+1))
      = (∑ i ∈ Finset.range 148, stT164 (i+1)) + stT164 149 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 148
    simpa using h
  have hprev := st164_p148
  have hstep := st164_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p150 : ((32853913539637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT164 (i+1))
      = (∑ i ∈ Finset.range 149, stT164 (i+1)) + stT164 150 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 149
    simpa using h
  have hprev := st164_p149
  have hstep := st164_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p151 : ((33667590864469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT164 (i+1))
      = (∑ i ∈ Finset.range 150, stT164 (i+1)) + stT164 151 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 150
    simpa using h
  have hprev := st164_p150
  have hstep := st164_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p152 : ((17028695927711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT164 (i+1))
      = (∑ i ∈ Finset.range 151, stT164 (i+1)) + stT164 152 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 151
    simpa using h
  have hprev := st164_p151
  have hstep := st164_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p153 : ((16809168600091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT164 (i+1))
      = (∑ i ∈ Finset.range 152, stT164 (i+1)) + stT164 153 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 152
    simpa using h
  have hprev := st164_p152
  have hstep := st164_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p154 : ((656290833017/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT164 (i+1))
      = (∑ i ∈ Finset.range 153, stT164 (i+1)) + stT164 154 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 153
    simpa using h
  have hprev := st164_p153
  have hstep := st164_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p155 : ((3247408641199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT164 (i+1))
      = (∑ i ∈ Finset.range 154, stT164 (i+1)) + stT164 155 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 154
    simpa using h
  have hprev := st164_p154
  have hstep := st164_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p156 : ((3293730068719/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT164 (i+1))
      = (∑ i ∈ Finset.range 155, stT164 (i+1)) + stT164 156 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 155
    simpa using h
  have hprev := st164_p155
  have hstep := st164_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p157 : ((8432953014999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT164 (i+1))
      = (∑ i ∈ Finset.range 156, stT164 (i+1)) + stT164 157 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 156
    simpa using h
  have hprev := st164_p156
  have hstep := st164_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p158 : ((34067302424681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT164 (i+1))
      = (∑ i ∈ Finset.range 157, stT164 (i+1)) + stT164 158 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 157
    simpa using h
  have hprev := st164_p157
  have hstep := st164_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p159 : ((33619910862453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT164 (i+1))
      = (∑ i ∈ Finset.range 158, stT164 (i+1)) + stT164 159 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 158
    simpa using h
  have hprev := st164_p158
  have hstep := st164_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p160 : ((32830574151653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT164 (i+1))
      = (∑ i ∈ Finset.range 159, stT164 (i+1)) + stT164 160 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 159
    simpa using h
  have hprev := st164_p159
  have hstep := st164_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p161 : ((6491613436523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT164 (i+1))
      = (∑ i ∈ Finset.range 160, stT164 (i+1)) + stT164 161 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 160
    simpa using h
  have hprev := st164_p160
  have hstep := st164_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p162 : ((1314024853599/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT164 (i+1))
      = (∑ i ∈ Finset.range 161, stT164 (i+1)) + stT164 162 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 161
    simpa using h
  have hprev := st164_p161
  have hstep := st164_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p163 : ((6726653452827/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT164 (i+1))
      = (∑ i ∈ Finset.range 162, stT164 (i+1)) + stT164 163 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 162
    simpa using h
  have hprev := st164_p162
  have hstep := st164_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p164 : ((1363121362383/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT164 (i+1))
      = (∑ i ∈ Finset.range 163, stT164 (i+1)) + stT164 164 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 163
    simpa using h
  have hprev := st164_p163
  have hstep := st164_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p165 : ((16890685333573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT164 (i+1))
      = (∑ i ∈ Finset.range 164, stT164 (i+1)) + stT164 165 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 164
    simpa using h
  have hprev := st164_p164
  have hstep := st164_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p166 : ((8254749086849/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT164 (i+1))
      = (∑ i ∈ Finset.range 165, stT164 (i+1)) + stT164 166 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 165
    simpa using h
  have hprev := st164_p165
  have hstep := st164_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p167 : ((8119409010353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT164 (i+1))
      = (∑ i ∈ Finset.range 166, stT164 (i+1)) + stT164 167 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 166
    simpa using h
  have hprev := st164_p166
  have hstep := st164_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p168 : ((203963473793/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT164 (i+1))
      = (∑ i ∈ Finset.range 167, stT164 (i+1)) + stT164 168 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 167
    simpa using h
  have hprev := st164_p167
  have hstep := st164_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p169 : ((1667233062511/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT164 (i+1))
      = (∑ i ∈ Finset.range 168, stT164 (i+1)) + stT164 169 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 168
    simpa using h
  have hprev := st164_p168
  have hstep := st164_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p170 : ((8497125362861/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT164 (i+1))
      = (∑ i ∈ Finset.range 169, stT164 (i+1)) + stT164 170 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 169
    simpa using h
  have hprev := st164_p169
  have hstep := st164_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p171 : ((6802970580693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT164 (i+1))
      = (∑ i ∈ Finset.range 170, stT164 (i+1)) + stT164 171 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 170
    simpa using h
  have hprev := st164_p170
  have hstep := st164_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p172 : ((16703683171471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT164 (i+1))
      = (∑ i ∈ Finset.range 171, stT164 (i+1)) + stT164 172 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 171
    simpa using h
  have hprev := st164_p171
  have hstep := st164_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p173 : ((2042586100293/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT164 (i+1))
      = (∑ i ∈ Finset.range 172, stT164 (i+1)) + stT164 173 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 172
    simpa using h
  have hprev := st164_p172
  have hstep := st164_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p174 : ((1013752618443/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT164 (i+1))
      = (∑ i ∈ Finset.range 173, stT164 (i+1)) + stT164 174 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 173
    simpa using h
  have hprev := st164_p173
  have hstep := st164_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p175 : ((1027399386627/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT164 (i+1))
      = (∑ i ∈ Finset.range 174, stT164 (i+1)) + stT164 175 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 174
    simpa using h
  have hprev := st164_p174
  have hstep := st164_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p176 : ((16815182325559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT164 (i+1))
      = (∑ i ∈ Finset.range 175, stT164 (i+1)) + stT164 176 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 175
    simpa using h
  have hprev := st164_p175
  have hstep := st164_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p177 : ((17046169906173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT164 (i+1))
      = (∑ i ∈ Finset.range 176, stT164 (i+1)) + stT164 177 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 176
    simpa using h
  have hprev := st164_p176
  have hstep := st164_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p178 : ((16949089772001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT164 (i+1))
      = (∑ i ∈ Finset.range 177, stT164 (i+1)) + stT164 178 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 177
    simpa using h
  have hprev := st164_p177
  have hstep := st164_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p179 : ((16603421550209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT164 (i+1))
      = (∑ i ∈ Finset.range 178, stT164 (i+1)) + stT164 179 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 178
    simpa using h
  have hprev := st164_p178
  have hstep := st164_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p180 : ((3256131039343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT164 (i+1))
      = (∑ i ∈ Finset.range 179, stT164 (i+1)) + stT164 180 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 179
    simpa using h
  have hprev := st164_p179
  have hstep := st164_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p181 : ((6491716364273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT164 (i+1))
      = (∑ i ∈ Finset.range 180, stT164 (i+1)) + stT164 181 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 180
    simpa using h
  have hprev := st164_p180
  have hstep := st164_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p182 : ((32971873033897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT164 (i+1))
      = (∑ i ∈ Finset.range 181, stT164 (i+1)) + stT164 182 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 181
    simpa using h
  have hprev := st164_p181
  have hstep := st164_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p183 : ((33707875465663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT164 (i+1))
      = (∑ i ∈ Finset.range 182, stT164 (i+1)) + stT164 183 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 182
    simpa using h
  have hprev := st164_p182
  have hstep := st164_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p184 : ((4264307713819/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT164 (i+1))
      = (∑ i ∈ Finset.range 183, stT164 (i+1)) + stT164 184 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 183
    simpa using h
  have hprev := st164_p183
  have hstep := st164_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p185 : ((16946944929201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT164 (i+1))
      = (∑ i ∈ Finset.range 184, stT164 (i+1)) + stT164 185 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 184
    simpa using h
  have hprev := st164_p184
  have hstep := st164_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p186 : ((16606741389483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT164 (i+1))
      = (∑ i ∈ Finset.range 185, stT164 (i+1)) + stT164 186 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 185
    simpa using h
  have hprev := st164_p185
  have hstep := st164_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p187 : ((1017836055511/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT164 (i+1))
      = (∑ i ∈ Finset.range 186, stT164 (i+1)) + stT164 187 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 186
    simpa using h
  have hprev := st164_p186
  have hstep := st164_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p188 : ((32426664682727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT164 (i+1))
      = (∑ i ∈ Finset.range 187, stT164 (i+1)) + stT164 188 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 187
    simpa using h
  have hprev := st164_p187
  have hstep := st164_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p189 : ((32879020311431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT164 (i+1))
      = (∑ i ∈ Finset.range 188, stT164 (i+1)) + stT164 189 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 188
    simpa using h
  have hprev := st164_p188
  have hstep := st164_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p190 : ((33604037085123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT164 (i+1))
      = (∑ i ∈ Finset.range 189, stT164 (i+1)) + stT164 190 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 189
    simpa using h
  have hprev := st164_p189
  have hstep := st164_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p191 : ((34094057316551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT164 (i+1))
      = (∑ i ∈ Finset.range 190, stT164 (i+1)) + stT164 191 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 190
    simpa using h
  have hprev := st164_p190
  have hstep := st164_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p192 : ((6802622991107/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT164 (i+1))
      = (∑ i ∈ Finset.range 191, stT164 (i+1)) + stT164 192 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 191
    simpa using h
  have hprev := st164_p191
  have hstep := st164_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p193 : ((33421646467231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT164 (i+1))
      = (∑ i ∈ Finset.range 192, stT164 (i+1)) + stT164 193 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 192
    simpa using h
  have hprev := st164_p192
  have hstep := st164_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p194 : ((3272440848193/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT164 (i+1))
      = (∑ i ∈ Finset.range 193, stT164 (i+1)) + stT164 194 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 193
    simpa using h
  have hprev := st164_p193
  have hstep := st164_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p195 : ((6477905035889/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT164 (i+1))
      = (∑ i ∈ Finset.range 194, stT164 (i+1)) + stT164 195 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 194
    simpa using h
  have hprev := st164_p194
  have hstep := st164_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p196 : ((6527193843743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT164 (i+1))
      = (∑ i ∈ Finset.range 195, stT164 (i+1)) + stT164 196 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 195
    simpa using h
  have hprev := st164_p195
  have hstep := st164_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p197 : ((1331862086641/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT164 (i+1))
      = (∑ i ∈ Finset.range 196, stT164 (i+1)) + stT164 197 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 196
    simpa using h
  have hprev := st164_p196
  have hstep := st164_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p198 : ((33937510222477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT164 (i+1))
      = (∑ i ∈ Finset.range 197, stT164 (i+1)) + stT164 198 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 197
    simpa using h
  have hprev := st164_p197
  have hstep := st164_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p199 : ((34145666039317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT164 (i+1))
      = (∑ i ∈ Finset.range 198, stT164 (i+1)) + stT164 199 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 198
    simpa using h
  have hprev := st164_p198
  have hstep := st164_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p200 : ((33791852323941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT164 (i+1))
      = (∑ i ∈ Finset.range 199, stT164 (i+1)) + stT164 200 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 199
    simpa using h
  have hprev := st164_p199
  have hstep := st164_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p201 : ((33104862953591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT164 (i+1))
      = (∑ i ∈ Finset.range 200, stT164 (i+1)) + stT164 201 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 200
    simpa using h
  have hprev := st164_p200
  have hstep := st164_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p202 : ((6503647342779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT164 (i+1))
      = (∑ i ∈ Finset.range 201, stT164 (i+1)) + stT164 202 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 201
    simpa using h
  have hprev := st164_p201
  have hstep := st164_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p203 : ((506177842383/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT164 (i+1))
      = (∑ i ∈ Finset.range 202, stT164 (i+1)) + stT164 203 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 202
    simpa using h
  have hprev := st164_p202
  have hstep := st164_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p204 : ((4100978773209/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT164 (i+1))
      = (∑ i ∈ Finset.range 203, stT164 (i+1)) + stT164 204 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 203
    simpa using h
  have hprev := st164_p203
  have hstep := st164_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p205 : ((4187438121339/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT164 (i+1))
      = (∑ i ∈ Finset.range 204, stT164 (i+1)) + stT164 205 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 204
    simpa using h
  have hprev := st164_p204
  have hstep := st164_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p206 : ((8512554167143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT164 (i+1))
      = (∑ i ∈ Finset.range 205, stT164 (i+1)) + stT164 206 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 205
    simpa using h
  have hprev := st164_p205
  have hstep := st164_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p207 : ((8532896484483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT164 (i+1))
      = (∑ i ∈ Finset.range 206, stT164 (i+1)) + stT164 207 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 206
    simpa using h
  have hprev := st164_p206
  have hstep := st164_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p208 : ((8424839901923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT164 (i+1))
      = (∑ i ∈ Finset.range 207, stT164 (i+1)) + stT164 208 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 207
    simpa using h
  have hprev := st164_p207
  have hstep := st164_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p209 : ((33011885512357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT164 (i+1))
      = (∑ i ∈ Finset.range 208, stT164 (i+1)) + stT164 209 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 208
    simpa using h
  have hprev := st164_p208
  have hstep := st164_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p210 : ((6494327672297/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT164 (i+1))
      = (∑ i ∈ Finset.range 209, stT164 (i+1)) + stT164 210 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 209
    simpa using h
  have hprev := st164_p209
  have hstep := st164_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p211 : ((16194553713839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT164 (i+1))
      = (∑ i ∈ Finset.range 210, stT164 (i+1)) + stT164 211 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 210
    simpa using h
  have hprev := st164_p210
  have hstep := st164_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p212 : ((1025237540561/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT164 (i+1))
      = (∑ i ∈ Finset.range 211, stT164 (i+1)) + stT164 212 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 211
    simpa using h
  have hprev := st164_p211
  have hstep := st164_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p213 : ((8371422173677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT164 (i+1))
      = (∑ i ∈ Finset.range 212, stT164 (i+1)) + stT164 213 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 212
    simpa using h
  have hprev := st164_p212
  have hstep := st164_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p214 : ((17020124880149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT164 (i+1))
      = (∑ i ∈ Finset.range 213, stT164 (i+1)) + stT164 214 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 213
    simpa using h
  have hprev := st164_p213
  have hstep := st164_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p215 : ((17081763497869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT164 (i+1))
      = (∑ i ∈ Finset.range 214, stT164 (i+1)) + stT164 215 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 214
    simpa using h
  have hprev := st164_p214
  have hstep := st164_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p216 : ((337910568051/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT164 (i+1))
      = (∑ i ∈ Finset.range 215, stT164 (i+1)) + stT164 216 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 215
    simpa using h
  have hprev := st164_p215
  have hstep := st164_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p217 : ((3313069132369/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT164 (i+1))
      = (∑ i ∈ Finset.range 216, stT164 (i+1)) + stT164 217 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 216
    simpa using h
  have hprev := st164_p216
  have hstep := st164_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p218 : ((16271438079431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT164 (i+1))
      = (∑ i ∈ Finset.range 217, stT164 (i+1)) + stT164 218 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 217
    simpa using h
  have hprev := st164_p217
  have hstep := st164_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p219 : ((3234296988337/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT164 (i+1))
      = (∑ i ∈ Finset.range 218, stT164 (i+1)) + stT164 219 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 218
    simpa using h
  have hprev := st164_p218
  have hstep := st164_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p220 : ((3263429127127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT164 (i+1))
      = (∑ i ∈ Finset.range 219, stT164 (i+1)) + stT164 220 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 219
    simpa using h
  have hprev := st164_p219
  have hstep := st164_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p221 : ((3325890758359/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT164 (i+1))
      = (∑ i ∈ Finset.range 220, stT164 (i+1)) + stT164 221 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 220
    simpa using h
  have hprev := st164_p220
  have hstep := st164_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p222 : ((677738970443/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT164 (i+1))
      = (∑ i ∈ Finset.range 221, stT164 (i+1)) + stT164 222 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 221
    simpa using h
  have hprev := st164_p221
  have hstep := st164_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p223 : ((8548064728031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT164 (i+1))
      = (∑ i ∈ Finset.range 222, stT164 (i+1)) + stT164 223 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 222
    simpa using h
  have hprev := st164_p222
  have hstep := st164_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p224 : ((1701012600949/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT164 (i+1))
      = (∑ i ∈ Finset.range 223, stT164 (i+1)) + stT164 224 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 223
    simpa using h
  have hprev := st164_p223
  have hstep := st164_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p225 : ((8365640268367/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT164 (i+1))
      = (∑ i ∈ Finset.range 224, stT164 (i+1)) + stT164 225 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 224
    simpa using h
  have hprev := st164_p224
  have hstep := st164_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p226 : ((512570950507/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT164 (i+1))
      = (∑ i ∈ Finset.range 225, stT164 (i+1)) + stT164 226 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 225
    simpa using h
  have hprev := st164_p225
  have hstep := st164_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p227 : ((252947026499/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT164 (i+1))
      = (∑ i ∈ Finset.range 226, stT164 (i+1)) + stT164 227 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 226
    simpa using h
  have hprev := st164_p226
  have hstep := st164_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p228 : ((16195698260067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT164 (i+1))
      = (∑ i ∈ Finset.range 227, stT164 (i+1)) + stT164 228 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 227
    simpa using h
  have hprev := st164_p227
  have hstep := st164_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p229 : ((16418274318009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT164 (i+1))
      = (∑ i ∈ Finset.range 228, stT164 (i+1)) + stT164 229 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 228
    simpa using h
  have hprev := st164_p228
  have hstep := st164_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p230 : ((16745693413289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT164 (i+1))
      = (∑ i ∈ Finset.range 229, stT164 (i+1)) + stT164 230 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 229
    simpa using h
  have hprev := st164_p229
  have hstep := st164_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p231 : ((2127276513979/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT164 (i+1))
      = (∑ i ∈ Finset.range 230, stT164 (i+1)) + stT164 231 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 230
    simpa using h
  have hprev := st164_p230
  have hstep := st164_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p232 : ((1710508869353/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT164 (i+1))
      = (∑ i ∈ Finset.range 231, stT164 (i+1)) + stT164 232 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 231
    simpa using h
  have hprev := st164_p231
  have hstep := st164_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p233 : ((16966296839537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT164 (i+1))
      = (∑ i ∈ Finset.range 232, stT164 (i+1)) + stT164 233 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 232
    simpa using h
  have hprev := st164_p232
  have hstep := st164_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p234 : ((16669304852027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT164 (i+1))
      = (∑ i ∈ Finset.range 233, stT164 (i+1)) + stT164 234 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 233
    simpa using h
  have hprev := st164_p233
  have hstep := st164_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p235 : ((32709606032107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT164 (i+1))
      = (∑ i ∈ Finset.range 234, stT164 (i+1)) + stT164 235 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 234
    simpa using h
  have hprev := st164_p234
  have hstep := st164_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p236 : ((32338810835537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT164 (i+1))
      = (∑ i ∈ Finset.range 235, stT164 (i+1)) + stT164 236 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 235
    simpa using h
  have hprev := st164_p235
  have hstep := st164_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p237 : ((32395511713547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT164 (i+1))
      = (∑ i ∈ Finset.range 236, stT164 (i+1)) + stT164 237 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 236
    simpa using h
  have hprev := st164_p236
  have hstep := st164_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p238 : ((8212603038077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT164 (i+1))
      = (∑ i ∈ Finset.range 237, stT164 (i+1)) + stT164 238 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 237
    simpa using h
  have hprev := st164_p237
  have hstep := st164_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p239 : ((16746825346083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT164 (i+1))
      = (∑ i ∈ Finset.range 238, stT164 (i+1)) + stT164 239 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 238
    simpa using h
  have hprev := st164_p238
  have hstep := st164_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p240 : ((17016850942117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT164 (i+1))
      = (∑ i ∈ Finset.range 239, stT164 (i+1)) + stT164 240 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 239
    simpa using h
  have hprev := st164_p239
  have hstep := st164_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p241 : ((17114874737261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT164 (i+1))
      = (∑ i ∈ Finset.range 240, stT164 (i+1)) + stT164 241 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 240
    simpa using h
  have hprev := st164_p240
  have hstep := st164_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p242 : ((33997390735897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT164 (i+1))
      = (∑ i ∈ Finset.range 241, stT164 (i+1)) + stT164 242 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 241
    simpa using h
  have hprev := st164_p241
  have hstep := st164_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p243 : ((6688432784477/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT164 (i+1))
      = (∑ i ∈ Finset.range 242, stT164 (i+1)) + stT164 243 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 242
    simpa using h
  have hprev := st164_p242
  have hstep := st164_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p244 : ((82022550793/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT164 (i+1))
      = (∑ i ∈ Finset.range 243, stT164 (i+1)) + stT164 244 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 243
    simpa using h
  have hprev := st164_p243
  have hstep := st164_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p245 : ((16186459521869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT164 (i+1))
      = (∑ i ∈ Finset.range 244, stT164 (i+1)) + stT164 245 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 244
    simpa using h
  have hprev := st164_p244
  have hstep := st164_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p246 : ((6463977205291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT164 (i+1))
      = (∑ i ∈ Finset.range 245, stT164 (i+1)) + stT164 246 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 245
    simpa using h
  have hprev := st164_p245
  have hstep := st164_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p247 : ((32669664703219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT164 (i+1))
      = (∑ i ∈ Finset.range 246, stT164 (i+1)) + stT164 247 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 246
    simpa using h
  have hprev := st164_p246
  have hstep := st164_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p248 : ((33271171628219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT164 (i+1))
      = (∑ i ∈ Finset.range 247, stT164 (i+1)) + stT164 248 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 247
    simpa using h
  have hprev := st164_p247
  have hstep := st164_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p249 : ((33869870336463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT164 (i+1))
      = (∑ i ∈ Finset.range 248, stT164 (i+1)) + stT164 249 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 248
    simpa using h
  have hprev := st164_p248
  have hstep := st164_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_p250 : ((34216225462843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT164 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT164 (i+1))
      = (∑ i ∈ Finset.range 249, stT164 (i+1)) + stT164 250 := by
    have h := Finset.sum_range_succ (fun i => stT164 (i+1)) 249
    simpa using h
  have hprev := st164_p249
  have hstep := st164_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st164_s250 :
    |Real.sin (((164 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))
      - ((209171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 2478001/10000000) (δ := 523/62500000) (ψ := -250289/1000000) 164 144
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 164`** (evaluated boundary). -/
theorem station_164_sign : hardyG ((((164:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 164 250 (by norm_num) (by norm_num)
    ((-250289/1000000 : ℚ) : ℝ)
  have hchain := st164_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT164 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((164 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-250289/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st164_c250
  have hsinb := abs_le.mp st164_s250
  have hbdy_lo : ((-2717549668977/33620312500000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((164 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ))) / 2
          - ((((164:ℕ)):ℝ))
            * Real.sin (((164 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-250289/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((164:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((164:ℝ) * Real.log (250:ℝ) - ((-250289/1000000 : ℚ) : ℝ))) / 2
        - ((164:ℝ)) * Real.sin ((164:ℝ) * Real.log (250:ℝ) - ((-250289/1000000 : ℚ) : ℝ))
        ≥ ((-34374561/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((164:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-34374561/250000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-34374561/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-34374561/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((164:ℕ)):ℝ))+1) * (((((164:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((38282482623/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((34216225462843/10000000000000 : ℚ) : ℝ) + ((-2717549668977/33620312500000 : ℚ) : ℝ)
      - ((38282482623/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-250289/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((164:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-250289/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((164:ℕ)):ℝ)))).re
      - Real.sin ((-250289/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((164:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((164:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((164:ℕ)):ℝ))
      = (((((164:ℕ)):ℝ)) * (Real.log ((((164:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((164:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_164
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
  have hθwin : |(((-250289/1000000 : ℚ) : ℝ) + ((30:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((164:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((164:ℕ)):ℝ)))
    (φ := ((-250289/1000000 : ℚ) : ℝ) + ((30:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-250289/1000000 : ℚ) : ℝ) + ((30:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-250289/1000000 : ℚ)) : ℝ) - Real.pi) + ((30:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-250289/1000000 : ℚ)) : ℝ) - Real.pi) 30).1,
    (cos_sin_shift ((((-250289/1000000 : ℚ)) : ℝ) - Real.pi) 30).2]
  exact cos_sin_flip ((-250289/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_164_sign
end AxiomAudit
