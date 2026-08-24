import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 272` (rung-280.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT272 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((272 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-29149/31250 : ℚ) : ℝ))

theorem st272_c1 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((595613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29149/125000) (δ := 1/1000000000) (ψ := -29149/31250) 272 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t1 : ((595563/1000000 : ℚ) : ℝ) ≤ stT272 1 := by
  have hc : ((595563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((595563/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((595563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c2 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((562629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608271/2500000) (δ := 13617/1000000000) (ψ := -29149/31250) 272 30
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t2 : ((3978033801793/10000000000000 : ℚ) : ℝ) ≤ stT272 2 := by
  have hc : ((562579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3978033801793/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((562579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c3 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-52729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4593987/10000000) (δ := 13657/1000000000) (ψ := -29149/31250) 272 48
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t3 : ((-304488774717/2000000000000 : ℚ) : ℝ) ≤ stT272 3 := by
  have hc : ((-52739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304488774717/2000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-52739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c4 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((528713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1267141/5000000) (δ := 213/15625000) (ψ := -29149/31250) 272 60
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t4 : ((528663/2000000 : ℚ) : ℝ) ≤ stT272 4 := by
  have hc : ((528663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((528663/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((528663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c5 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((432907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2807703/10000000) (δ := 13699/1000000000) (ψ := -29149/31250) 272 70
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t5 : ((387158987939/2000000000000 : ℚ) : ℝ) ≤ stT272 5 := by
  have hc : ((432857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387158987939/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((432857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c6 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-28049/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4492789/10000000) (δ := 13641/1000000000) (ψ := -29149/31250) 272 78
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t6 : ((-458140324743/5000000000000 : ℚ) : ℝ) ≤ stT272 6 := by
  have hc : ((-112221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-458140324743/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-112221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c7 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-189781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6081907/10000000) (δ := 6899/500000000) (ψ := -29149/31250) 272 84
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t7 : ((-286940821323/1000000000000 : ℚ) : ℝ) ≤ stT272 7 := by
  have hc : ((-379587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286940821323/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-379587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c8 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((49393/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65887/250000) (δ := 853/62500000) (ψ := -29149/31250) 272 90
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t8 : ((43653225951/250000000000 : ℚ) : ℝ) ≤ stT272 8 := by
  have hc : ((12347/25000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43653225951/250000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((12347/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c9 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-20851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 523513/1250000) (δ := 1723/125000000) (ψ := -29149/31250) 272 95
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t9 : ((-34768340287/1000000000000 : ℚ) : ℝ) ≤ stT272 9 := by
  have hc : ((-20861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34768340287/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-20861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c10 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((29313/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2706573/10000000) (δ := 3421/250000000) (ψ := -29149/31250) 272 100
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t10 : ((741487548683/5000000000000 : ℚ) : ℝ) ≤ stT272 10 := by
  have hc : ((234479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((741487548683/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((234479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c11 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((957959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72749/1000000) (δ := 2731/200000000) (ψ := -29149/31250) 272 104
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t11 : ((2888203878717/10000000000000 : ℚ) : ℝ) ≤ stT272 11 := by
  have hc : ((957909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2888203878717/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((957909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c12 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-46193/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4391591/10000000) (δ := 6813/500000000) (ψ := -29149/31250) 272 108
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t12 : ((-8336488721/156250000000 : ℚ) : ℝ) ≤ stT272 12 := by
  have hc : ((-92411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8336488721/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-92411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c13 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((394363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 582711/2000000) (δ := 2741/200000000) (ψ := -29149/31250) 272 111
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t13 : ((2187254211/20000000000 : ℚ) : ℝ) ≤ stT272 13 := by
  have hc : ((394313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2187254211/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((394313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c14 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-156969/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1236621/2000000) (δ := 13783/1000000000) (ψ := -29149/31250) 272 114
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t14 : ((-419544116127/2000000000000 : ℚ) : ℝ) ≤ stT272 14 := by
  have hc : ((-156979/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419544116127/2000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-156979/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c15 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-146087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493597/2500000) (δ := 6871/500000000) (ψ := -29149/31250) 272 117
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t15 : ((-377220846933/2000000000000 : ℚ) : ℝ) ≤ stT272 15 := by
  have hc : ((-146097/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377220846933/2000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-146097/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c16 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((458339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1368339/5000000) (δ := 13663/1000000000) (ψ := -29149/31250) 272 120
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t16 : ((458289/4000000 : ℚ) : ℝ) ≤ stT272 16 := by
  have hc : ((458289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458289/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((458289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c17 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((301059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -790621/2500000) (δ := 6809/500000000) (ψ := -29149/31250) 272 123
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t17 : ((182513496051/2500000000000 : ℚ) : ℝ) ≤ stT272 17 := by
  have hc : ((301009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182513496051/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((301009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c18 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-72209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2144651/5000000) (δ := 13799/1000000000) (ψ := -29149/31250) 272 125
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t18 : ((-85128599691/2500000000000 : ℚ) : ℝ) ≤ stT272 18 := by
  have hc : ((-36117/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85128599691/2500000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-36117/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c19 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-30229/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1517223/2500000) (δ := 343/25000000) (ψ := -29149/31250) 272 128
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t19 : ((-34677345249/200000000000 : ℚ) : ℝ) ≤ stT272 19 := by
  have hc : ((-30231/40000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34677345249/200000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-30231/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c20 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((100873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20843/80000) (δ := 3417/250000000) (ψ := -29149/31250) 272 130
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t20 : ((225536425821/2000000000000 : ℚ) : ℝ) ≤ stT272 20 := by
  have hc : ((100863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225536425821/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((100863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c21 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((943557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168793/2000000) (δ := 13749/1000000000) (ψ := -29149/31250) 272 132
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t21 : ((1029450109123/5000000000000 : ℚ) : ℝ) ≤ stT272 21 := by
  have hc : ((943507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1029450109123/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((943507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c22 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((60549/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156573/2500000) (δ := 13639/1000000000) (ψ := -29149/31250) 272 134
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t22 : ((1032673834569/5000000000000 : ℚ) : ℝ) ≤ stT272 22 := by
  have hc : ((484367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1032673834569/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((484367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c23 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((373919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -907497/5000000) (δ := 6889/500000000) (ψ := -29149/31250) 272 136
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t23 : ((48726426921/312500000000 : ℚ) : ℝ) ≤ stT272 23 := by
  have hc : ((186947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48726426921/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((186947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c24 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-2897/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4290393/10000000) (δ := 13611/1000000000) (ψ := -29149/31250) 272 138
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t24 : ((-1478879829/50000000000 : ℚ) : ℝ) ≤ stT272 24 := by
  have hc : ((-1449/10000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1478879829/50000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-1449/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c25 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-999303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1940151/2500000) (δ := 13699/1000000000) (ψ := -29149/31250) 272 139
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t25 : ((-1998706999353/10000000000000 : ℚ) : ℝ) ≤ stT272 25 := by
  have hc : ((-999353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1998706999353/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-999353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c26 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((356851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3014753/10000000) (δ := 13689/1000000000) (ψ := -29149/31250) 272 141
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t26 : ((699744205961/10000000000000 : ℚ) : ℝ) ≤ stT272 26 := by
  have hc : ((356801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699744205961/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((356801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c27 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((457951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2737769/10000000) (δ := 429/31250000) (ψ := -29149/31250) 272 143
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t27 : ((1762460949/20000000000 : ℚ) : ℝ) ≤ stT272 27 := by
  have hc : ((457901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1762460949/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((457901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c28 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-2529/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6284303/10000000) (δ := 1721/125000000) (ψ := -29149/31250) 272 144
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t28 : ((-152949044859/1000000000000 : ℚ) : ℝ) ≤ stT272 28 := by
  have hc : ((-80933/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152949044859/1000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-80933/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c29 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((873809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1269539/10000000) (δ := 273/20000000) (ψ := -29149/31250) 272 146
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t29 : ((1622529396327/10000000000000 : ℚ) : ℝ) ≤ stT272 29 := by
  have hc : ((873759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1622529396327/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((873759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c30 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-378729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3037759/5000000) (δ := 13757/1000000000) (ψ := -29149/31250) 272 147
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t30 : ((-172876771367/1250000000000 : ℚ) : ℝ) ≤ stT272 30 := by
  have hc : ((-189377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172876771367/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-189377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c31 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((34617/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3043277/10000000) (δ := 213/15625000) (ψ := -29149/31250) 272 149
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t31 : ((15541246609/250000000000 : ℚ) : ℝ) ≤ stT272 31 := by
  have hc : ((8653/25000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15541246609/250000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((8653/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c32 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((105499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 709469/2500000) (δ := 6839/500000000) (ψ := -29149/31250) 272 150
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t32 : ((186475448159/2500000000000 : ℚ) : ℝ) ≤ stT272 32 := by
  have hc : ((210973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186475448159/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((210973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c33 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-498391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7653363/10000000) (δ := 1371/100000000) (ψ := -29149/31250) 272 152
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t33 : ((-54226944327/312500000000 : ℚ) : ℝ) ≤ stT272 33 := by
  have hc : ((-31151/31250 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54226944327/312500000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-31151/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c34 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((339403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1530643/5000000) (δ := 13603/1000000000) (ψ := -29149/31250) 272 153
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t34 : ((116397060941/2000000000000 : ℚ) : ℝ) ≤ stT272 34 := by
  have hc : ((339353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116397060941/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((339353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c35 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((92981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 942251/10000000) (δ := 13707/1000000000) (ψ := -29149/31250) 272 154
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t35 : ((2455594947/15625000000 : ℚ) : ℝ) ≤ stT272 35 := by
  have hc : ((5811/6250 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2455594947/15625000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((5811/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c36 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-184343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4390499/10000000) (δ := 13789/1000000000) (ψ := -29149/31250) 272 155
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t36 : ((-307321728131/10000000000000 : ℚ) : ℝ) ≤ stT272 36 := by
  have hc : ((-184393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307321728131/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-184393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c37 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-61047/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114279/156250) (δ := 13681/1000000000) (ψ := -29149/31250) 272 156
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t37 : ((-80292635999/500000000000 : ℚ) : ℝ) ≤ stT272 37 := by
  have hc : ((-488401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80292635999/500000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-488401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c38 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-182151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2983847/5000000) (δ := 1717/125000000) (ψ := -29149/31250) 272 158
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t38 : ((-118203344861/1000000000000 : ℚ) : ℝ) ≤ stT272 38 := by
  have hc : ((-364327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118203344861/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-364327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c39 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-8531/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2006159/5000000) (δ := 43/3125000) (ψ := -29149/31250) 272 159
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t39 : ((-13680552767/2500000000000 : ℚ) : ℝ) ≤ stT272 39 := by
  have hc : ((-17087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13680552767/2500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-17087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c40 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((33681/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2504177/10000000) (δ := 13653/1000000000) (ψ := -29149/31250) 272 160
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t40 : ((212997471687/2500000000000 : ℚ) : ℝ) ≤ stT272 40 := by
  have hc : ((269423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212997471687/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((269423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c41 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((421363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -355293/2500000) (δ := 13657/1000000000) (ψ := -29149/31250) 272 161
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t41 : ((329009572053/2500000000000 : ℚ) : ℝ) ≤ stT272 41 := by
  have hc : ((210669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329009572053/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((210669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c42 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((956187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742767/10000000) (δ := 2753/200000000) (ψ := -29149/31250) 272 162
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t42 : ((1475350943521/10000000000000 : ℚ) : ℝ) ≤ stT272 42 := by
  have hc : ((956137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1475350943521/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((956137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c43 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((245961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449991/10000000) (δ := 13731/1000000000) (ψ := -29149/31250) 272 163
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t43 : ((150027109309/1000000000000 : ℚ) : ℝ) ≤ stT272 43 := by
  have hc : ((491897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150027109309/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((491897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c44 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((978023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262547/5000000) (δ := 1703/125000000) (ψ := -29149/31250) 272 164
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t44 : ((368587265997/2500000000000 : ℚ) : ℝ) ≤ stT272 44 := by
  have hc : ((977973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368587265997/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((977973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c45 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((464217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -951553/10000000) (δ := 6843/500000000) (ψ := -29149/31250) 272 165
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t45 : ((10812126883/78125000000 : ℚ) : ℝ) ≤ stT272 45 := by
  have hc : ((14506/15625 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10812126883/78125000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((14506/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c46 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((387037/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214233/1250000) (δ := 13793/1000000000) (ψ := -29149/31250) 272 166
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t46 : ((142654461507/1250000000000 : ℚ) : ℝ) ≤ stT272 46 := by
  have hc : ((96753/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142654461507/1250000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((96753/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c47 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((218283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349693/1250000) (δ := 13703/1000000000) (ψ := -29149/31250) 272 167
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t47 : ((159180906721/2500000000000 : ℚ) : ℝ) ≤ stT272 47 := by
  have hc : ((109129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159180906721/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((109129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c48 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-104689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837839/2000000) (δ := 1701/125000000) (ψ := -29149/31250) 272 168
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t48 : ((-9448609929/625000000000 : ℚ) : ℝ) ≤ stT272 48 := by
  have hc : ((-104739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9448609929/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-104739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c49 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-703027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2938051/5000000) (δ := 2743/200000000) (ψ := -29149/31250) 272 169
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t49 : ((-251099029011/2500000000000 : ℚ) : ℝ) ≤ stT272 49 := by
  have hc : ((-703077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251099029011/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-703077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c50 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-199999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3923081/5000000) (δ := 13781/1000000000) (ψ := -29149/31250) 272 170
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t50 : ((-141427763963/1000000000000 : ℚ) : ℝ) ≤ stT272 50 := by
  have hc : ((-200009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141427763963/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-200009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c51 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-626493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2809803/5000000) (δ := 13781/1000000000) (ψ := -29149/31250) 272 170
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t51 : ((-877336258583/10000000000000 : ℚ) : ℝ) ≤ stT272 51 := by
  have hc : ((-626543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-877336258583/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-626543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c52 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((63751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3115951/10000000) (δ := 6837/500000000) (ψ := -29149/31250) 272 171
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t52 : ((353571327/8000000000 : ℚ) : ℝ) ≤ stT272 52 := by
  have hc : ((63741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353571327/8000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((63741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c53 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((494803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90191/2500000) (δ := 3409/250000000) (ψ := -29149/31250) 272 172
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t53 : ((67962953469/500000000000 : ℚ) : ℝ) ≤ stT272 53 := by
  have hc : ((247389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67962953469/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((247389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c54 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((493551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2636571/10000000) (δ := 859/62500000) (ψ := -29149/31250) 272 173
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t54 : ((671569485327/10000000000000 : ℚ) : ℝ) ≤ stT272 54 := by
  have hc : ((493501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671569485327/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((493501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c55 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-28019/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5867147/10000000) (δ := 1719/125000000) (ψ := -29149/31250) 272 174
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t55 : ((-94458791/1000000000 : ℚ) : ℝ) ≤ stT272 55 := by
  have hc : ((-28021/40000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94458791/1000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-28021/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c56 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-416187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6385433/10000000) (δ := 1719/125000000) (ψ := -29149/31250) 272 174
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t56 : ((-139046752271/1250000000000 : ℚ) : ℝ) ≤ stT272 56 := by
  have hc : ((-104053/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139046752271/1250000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-104053/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c57 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((233333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1356599/5000000) (δ := 2729/200000000) (ψ := -29149/31250) 272 175
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t57 : ((19313994491/312500000000 : ℚ) : ℝ) ≤ stT272 57 := by
  have hc : ((58327/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19313994491/312500000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((58327/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c58 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((892771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1168341/10000000) (δ := 2733/200000000) (ψ := -29149/31250) 272 176
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t58 : ((146524975893/1250000000000 : ℚ) : ℝ) ≤ stT272 58 := by
  have hc : ((892721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146524975893/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((892721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c59 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-20223/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328257/625000) (δ := 3443/250000000) (ψ := -29149/31250) 272 177
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t59 : ((-105322901/1600000000 : ℚ) : ℝ) ≤ stT272 59 := by
  have hc : ((-809/1600 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105322901/1600000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-809/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c60 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-783259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1544179/2500000) (δ := 3443/250000000) (ψ := -29149/31250) 272 177
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t60 : ((-202249600491/2000000000000 : ℚ) : ℝ) ≤ stT272 60 := by
  have hc : ((-783309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202249600491/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-783309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c61 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((387693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 427169/2500000) (δ := 3431/250000000) (ψ := -29149/31250) 272 178
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t61 : ((7755589091/78125000000 : ℚ) : ℝ) ≤ stT272 61 := by
  have hc : ((96917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7755589091/78125000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((96917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c62 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((383827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2942147/10000000) (δ := 851/62500000) (ψ := -29149/31250) 272 179
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t62 : ((487397173777/10000000000000 : ℚ) : ℝ) ≤ stT272 62 := by
  have hc : ((383777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487397173777/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((383777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c63 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-499717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3884919/5000000) (δ := 6847/500000000) (ψ := -29149/31250) 272 180
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t63 : ((-157403987611/1250000000000 : ℚ) : ℝ) ≤ stT272 63 := by
  have hc : ((-249871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157403987611/1250000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-249871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c64 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((384987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1469503/5000000) (δ := 6847/500000000) (ψ := -29149/31250) 272 180
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t64 : ((384937/8000000 : ℚ) : ℝ) ≤ stT272 64 := by
  have hc : ((384937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384937/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((384937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c65 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((62907/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2226101/10000000) (δ := 13801/1000000000) (ψ := -29149/31250) 272 181
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t65 : ((39010153497/500000000000 : ℚ) : ℝ) ≤ stT272 65 := by
  have hc : ((31451/50000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39010153497/500000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((31451/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c66 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-992721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1510433/2000000) (δ := 2739/200000000) (ψ := -29149/31250) 272 182
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t66 : ((-244403343093/2000000000000 : ℚ) : ℝ) ≤ stT272 66 := by
  have hc : ((-992771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244403343093/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-992771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c67 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((480613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2673607/10000000) (δ := 2739/200000000) (ψ := -29149/31250) 272 182
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t67 : ((293550466861/5000000000000 : ℚ) : ℝ) ≤ stT272 67 := by
  have hc : ((480563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293550466861/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((480563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c68 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((377191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -370011/1250000) (δ := 2723/200000000) (ψ := -29149/31250) 272 183
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t68 : ((228675296799/5000000000000 : ℚ) : ℝ) ≤ stT272 68 := by
  have hc : ((377141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228675296799/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((377141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c69 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-234433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 870887/1250000) (δ := 2723/200000000) (ψ := -29149/31250) 272 183
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t69 : ((-564478650369/5000000000000 : ℚ) : ℝ) ≤ stT272 69 := by
  have hc : ((-468891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564478650369/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-468891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c70 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((457077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1043449/10000000) (δ := 13723/1000000000) (ψ := -29149/31250) 272 184
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t70 : ((34142584241/312500000000 : ℚ) : ℝ) ≤ stT272 70 := by
  have hc : ((114263/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34142584241/312500000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((114263/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c71 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-423041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5018987/10000000) (δ := 13773/1000000000) (ψ := -29149/31250) 272 185
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t71 : ((-251058391581/5000000000000 : ℚ) : ℝ) ≤ stT272 71 := by
  have hc : ((-423091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251058391581/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-423091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c72 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-223967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4491697/10000000) (δ := 13773/1000000000) (ψ := -29149/31250) 272 185
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t72 : ((-16500420169/625000000000 : ℚ) : ℝ) ≤ stT272 72 := by
  have hc : ((-224017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16500420169/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-224017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c73 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((742013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -918411/5000000) (δ := 6833/500000000) (ψ := -29149/31250) 272 186
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t73 : ((868401656793/10000000000000 : ℚ) : ℝ) ≤ stT272 73 := by
  have hc : ((741963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((868401656793/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((741963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c74 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-492311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3707493/5000000) (δ := 6833/500000000) (ψ := -29149/31250) 272 186
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t74 : ((-35770579767/312500000000 : ℚ) : ℝ) ≤ stT272 74 := by
  have hc : ((-30771/31250 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35770579767/312500000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-30771/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c75 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((472387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 834731/10000000) (δ := 3411/250000000) (ψ := -29149/31250) 272 187
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t75 : ((2727182007/25000000000 : ℚ) : ℝ) ≤ stT272 75 := by
  have hc : ((236181/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2727182007/25000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((236181/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c76 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-700289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45832/78125) (δ := 13751/1000000000) (ψ := -29149/31250) 272 188
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t76 : ((-803344159781/10000000000000 : ℚ) : ℝ) ≤ stT272 76 := by
  have hc : ((-700339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-803344159781/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-700339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c77 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((353943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 755633/2500000) (δ := 13751/1000000000) (ψ := -29149/31250) 272 188
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t77 : ((80659646453/2000000000000 : ℚ) : ℝ) ≤ stT272 77 := by
  have hc : ((353893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80659646453/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((353893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c78 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((1587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48889/125000) (δ := 2749/200000000) (ψ := -29149/31250) 272 189
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t78 : ((3565540273/5000000000000 : ℚ) : ℝ) ≤ stT272 78 := by
  have hc : ((3149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3565540273/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((3149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c79 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-323819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23757/50000) (δ := 2749/200000000) (ψ := -29149/31250) 272 189
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t79 : ((-11386910171/312500000000 : ℚ) : ℝ) ≤ stT272 79 := by
  have hc : ((-323869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11386910171/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-323869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c80 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((572543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2402979/10000000) (δ := 13637/1000000000) (ψ := -29149/31250) 272 190
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t80 : ((640066066269/10000000000000 : ℚ) : ℝ) ≤ stT272 80 := by
  have hc : ((572493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((640066066269/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((572493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c81 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-187313/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6044321/10000000) (δ := 13637/1000000000) (ψ := -29149/31250) 272 190
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t81 : ((-52034902739/625000000000 : ℚ) : ℝ) ≤ stT272 81 := by
  have hc : ((-374651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52034902739/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-374651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c82 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((431911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -659987/5000000) (δ := 13673/1000000000) (ψ := -29149/31250) 272 191
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t82 : ((47693818809/500000000000 : ℚ) : ℝ) ≤ stT272 82 := by
  have hc : ((215943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47693818809/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((215943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c83 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-465699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3461289/5000000) (δ := 13673/1000000000) (ψ := -29149/31250) 272 191
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t83 : ((-127799672133/1250000000000 : ℚ) : ℝ) ≤ stT272 83 := by
  have hc : ((-116431/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127799672133/1250000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-116431/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c84 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((60453/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641603/10000000) (δ := 1369/50000000) (ψ := -29149/31250) 272 192
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t84 : ((527649549311/5000000000000 : ℚ) : ℝ) ≤ stT272 84 := by
  have hc : ((483599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527649549311/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((483599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c85 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-39359/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7405823/10000000) (δ := 689/50000000) (ψ := -29149/31250) 272 192
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t85 : ((-42693026733/400000000000 : ℚ) : ℝ) ≤ stT272 85 := by
  have hc : ((-39361/40000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42693026733/400000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-39361/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c86 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((990279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -348861/10000000) (δ := 3429/250000000) (ψ := -29149/31250) 272 193
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t86 : ((1067790666883/10000000000000 : ℚ) : ℝ) ≤ stT272 86 := by
  have hc : ((990229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1067790666883/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((990229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c87 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-30959/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7512551/10000000) (δ := 3429/250000000) (ψ := -29149/31250) 272 193
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t87 : ((-531091544697/5000000000000 : ℚ) : ℝ) ≤ stT272 87 := by
  have hc : ((-495369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-531091544697/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-495369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c88 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((985659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52987/1250000) (δ := 13609/1000000000) (ψ := -29149/31250) 272 194
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t88 : ((1050662150827/10000000000000 : ℚ) : ℝ) ≤ stT272 88 := by
  have hc : ((985609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1050662150827/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((985609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c89 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-194377/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1814941/2500000) (δ := 13609/1000000000) (ψ := -29149/31250) 272 194
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t89 : ((-103024915613/1000000000000 : ℚ) : ℝ) ≤ stT272 89 := by
  have hc : ((-194387/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103024915613/1000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-194387/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c90 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((942707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170071/2000000) (δ := 6851/500000000) (ψ := -29149/31250) 272 195
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t90 : ((248411800611/2500000000000 : ℚ) : ℝ) ≤ stT272 90 := by
  have hc : ((942657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248411800611/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((942657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c91 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-177751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6663543/10000000) (δ := 13651/500000000) (ψ := -29149/31250) 272 195
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t91 : ((-37268837977/400000000000 : ℚ) : ℝ) ≤ stT272 91 := by
  have hc : ((-177761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37268837977/400000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-177761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c92 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((39953/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1612667/10000000) (δ := 6897/500000000) (ψ := -29149/31250) 272 196
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t92 : ((20825636343/250000000000 : ℚ) : ℝ) ≤ stT272 92 := by
  have hc : ((79901/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20825636343/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((79901/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c93 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-10358/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1147749/2000000) (δ := 6897/500000000) (ψ := -29149/31250) 272 196
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t93 : ((-42966235739/625000000000 : ℚ) : ℝ) ≤ stT272 93 := by
  have hc : ((-331481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42966235739/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-331481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c94 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((472593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1348207/5000000) (δ := 13687/1000000000) (ψ := -29149/31250) 272 197
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t94 : ((487390773603/10000000000000 : ℚ) : ℝ) ≤ stT272 94 := by
  have hc : ((472543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487390773603/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((472543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c95 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-113487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2249707/5000000) (δ := 13687/1000000000) (ψ := -29149/31250) 272 197
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t95 : ((-14557616031/625000000000 : ℚ) : ℝ) ≤ stT272 95 := by
  have hc : ((-14189/62500 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14557616031/625000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-14189/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c96 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-12877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -817613/2000000) (δ := 13623/1000000000) (ψ := -29149/31250) 272 198
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t96 : ((-13152742827/2000000000000 : ℚ) : ℝ) ≤ stT272 96 := by
  have hc : ((-12887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13152742827/2000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-12887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c97 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((377727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2958639/10000000) (δ := 13623/1000000000) (ψ := -29149/31250) 272 198
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t97 : ((191736415621/5000000000000 : ℚ) : ℝ) ≤ stT272 97 := by
  have hc : ((377677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191736415621/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((377677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c98 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-673671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -721863/1250000) (δ := 1373/100000000) (ψ := -29149/31250) 272 199
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t98 : ((-680561289313/10000000000000 : ℚ) : ℝ) ≤ stT272 98 := by
  have hc : ((-673721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-680561289313/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-673721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c99 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((899797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141091/1250000) (δ := 1373/100000000) (ψ := -29149/31250) 272 199
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t99 : ((904279025639/10000000000000 : ℚ) : ℝ) ≤ stT272 99 := by
  have hc : ((899747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((904279025639/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((899747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c100 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-999051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -968129/1250000) (δ := 6883/500000000) (ψ := -29149/31250) 272 200
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t100 : ((-999101/10000000 : ℚ) : ℝ) ≤ stT272 100 := by
  have hc : ((-999101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-999101/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-999101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c101 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((57771/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24469/250000) (δ := 6883/500000000) (ψ := -29149/31250) 272 200
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t101 : ((459849384291/5000000000000 : ℚ) : ℝ) ≤ stT272 101 := by
  have hc : ((462143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459849384291/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((462143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c102 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-328761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1430201/2500000) (δ := 6883/500000000) (ψ := -29149/31250) 272 200
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t102 : ((-40693350041/625000000000 : ℚ) : ℝ) ≤ stT272 102 := by
  have hc : ((-164393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40693350041/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-164393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c103 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((11379/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3353011/10000000) (δ := 6829/500000000) (ψ := -29149/31250) 272 201
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t103 : ((22419190737/1000000000000 : ℚ) : ℝ) ≤ stT272 103 := by
  have hc : ((22753/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22419190737/1000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((22753/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c104 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((280163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3217081/10000000) (δ := 6829/500000000) (ψ := -29149/31250) 272 201
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t104 : ((13733660277/500000000000 : ℚ) : ℝ) ≤ stT272 104 := by
  have hc : ((280113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13733660277/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((280113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c105 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-732953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2991811/5000000) (δ := 3413/250000000) (ψ := -29149/31250) 272 202
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t105 : ((-715338360703/10000000000000 : ℚ) : ℝ) ≤ stT272 105 := by
  have hc : ((-733003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-715338360703/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-733003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c106 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((982981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230947/5000000) (δ := 3413/250000000) (ψ := -29149/31250) 272 202
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t106 : ((190941227267/2000000000000 : ℚ) : ℝ) ≤ stT272 106 := by
  have hc : ((982931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190941227267/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((982931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c107 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-919963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3423479/5000000) (δ := 3413/250000000) (ψ := -29149/31250) 272 202
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t107 : ((-889410607581/10000000000000 : ℚ) : ℝ) ≤ stT272 107 := by
  have hc : ((-920013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-889410607581/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-920013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c108 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((264171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2535373/10000000) (δ := 13759/1000000000) (ψ := -29149/31250) 272 203
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t108 : ((508348977/10000000000 : ℚ) : ℝ) ≤ stT272 108 := by
  have hc : ((132073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((508348977/10000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((132073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c109 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((77951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 746383/2000000) (δ := 13759/1000000000) (ψ := -29149/31250) 272 203
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t109 : ((37307801613/5000000000000 : ℚ) : ℝ) ≤ stT272 109 := by
  have hc : ((77901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37307801613/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((77901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c110 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-33551/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5765949/10000000) (δ := 13737/1000000000) (ψ := -29149/31250) 272 204
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t110 : ((-63984041541/1000000000000 : ℚ) : ℝ) ≤ stT272 110 := by
  have hc : ((-67107/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63984041541/1000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-67107/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c111 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((493991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 387983/10000000) (δ := 13737/1000000000) (ψ := -29149/31250) 272 204
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t111 : ((234425643331/2500000000000 : ℚ) : ℝ) ≤ stT272 111 := by
  have hc : ((246983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234425643331/2500000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((246983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c112 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-21353/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6486631/10000000) (δ := 13737/1000000000) (ψ := -29149/31250) 272 204
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t112 : ((-5044471769/62500000000 : ℚ) : ℝ) ≤ stT272 112 := by
  have hc : ((-85417/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5044471769/62500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-85417/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c113 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((295589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794203/2500000) (δ := 1363/100000000) (ψ := -29149/31250) 272 205
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t113 : ((3475243101/125000000000 : ℚ) : ℝ) ≤ stT272 113 := by
  have hc : ((295539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3475243101/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((295539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c114 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((107623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 703599/2500000) (δ := 1363/100000000) (ψ := -29149/31250) 272 205
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t114 : ((40314552057/1000000000000 : ℚ) : ℝ) ≤ stT272 114 := by
  have hc : ((215221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40314552057/1000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((215221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c115 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-935991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6954651/10000000) (δ := 171/12500000) (ψ := -29149/31250) 272 206
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t115 : ((-174572582541/2000000000000 : ℚ) : ℝ) ≤ stT272 115 := by
  have hc : ((-936041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174572582541/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-936041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c116 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((45513/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1067211/10000000) (δ := 171/12500000) (ψ := -29149/31250) 272 206
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t116 : ((21127703499/250000000000 : ℚ) : ℝ) ≤ stT272 116 := by
  have hc : ((91021/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21127703499/250000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((91021/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c117 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-82691/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4769773/10000000) (δ := 171/12500000) (ψ := -29149/31250) 272 206
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t117 : ((-152918936907/5000000000000 : ℚ) : ℝ) ≤ stT272 117 := by
  have hc : ((-165407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152918936907/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-165407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c118 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-235123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2575457/5000000) (δ := 3447/250000000) (ψ := -29149/31250) 272 207
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t118 : ((-2164713701/50000000000 : ℚ) : ℝ) ≤ stT272 118 := by
  have hc : ((-58787/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2164713701/50000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-58787/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c119 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((972517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58747/1000000) (δ := 3447/250000000) (ψ := -29149/31250) 272 207
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t119 : ((445729276983/5000000000000 : ℚ) : ℝ) ≤ stT272 119 := by
  have hc : ((972467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445729276983/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((972467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c120 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-25243/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3138957/5000000) (δ := 3447/250000000) (ψ := -29149/31250) 272 207
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t120 : ((-368720464223/5000000000000 : ℚ) : ℝ) ≤ stT272 120 := by
  have hc : ((-403913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368720464223/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-403913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c121 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((56021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1893433/5000000) (δ := 3427/250000000) (ψ := -29149/31250) 272 208
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t121 : ((5088267639/1000000000000 : ℚ) : ℝ) ≤ stT272 121 := by
  have hc : ((55971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5088267639/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((55971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c122 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((187299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904937/5000000) (δ := 3427/250000000) (ψ := -29149/31250) 272 208
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t122 : ((339122287561/5000000000000 : ℚ) : ℝ) ≤ stT272 122 := by
  have hc : ((374573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339122287561/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((374573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c123 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-490307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3680459/5000000) (δ := 3427/250000000) (ψ := -29149/31250) 272 208
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t123 : ((-11052941361/125000000000 : ℚ) : ℝ) ≤ stT272 123 := by
  have hc : ((-122583/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11052941361/125000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-122583/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c124 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((420881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2840949/10000000) (δ := 6801/500000000) (ψ := -29149/31250) 272 209
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t124 : ((188958589803/5000000000000 : ℚ) : ℝ) ≤ stT272 124 := by
  have hc : ((420831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188958589803/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((420831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c125 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((498977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2620947/10000000) (δ := 6801/500000000) (ψ := -29149/31250) 272 209
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t125 : ((446253779829/10000000000000 : ℚ) : ℝ) ≤ stT272 125 := by
  have hc : ((498927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446253779829/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((498927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c126 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-997253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47929/62500) (δ := 13709/1000000000) (ψ := -29149/31250) 272 210
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t126 : ((-888468320913/10000000000000 : ℚ) : ℝ) ≤ stT272 126 := by
  have hc : ((-997303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-888468320913/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-997303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c127 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((607991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -573293/2500000) (δ := 13709/1000000000) (ψ := -29149/31250) 272 210
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t127 : ((134865023499/2500000000000 : ℚ) : ℝ) ≤ stT272 127 := by
  have hc : ((607941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134865023499/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((607941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c128 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((347323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 760051/2500000) (δ := 13709/1000000000) (ψ := -29149/31250) 272 210
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t128 : ((306948701059/10000000000000 : ℚ) : ℝ) ≤ stT272 128 := by
  have hc : ((347273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306948701059/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((347273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c129 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-122721/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -921983/1250000) (δ := 13787/1000000000) (ψ := -29149/31250) 272 211
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t129 : ((-432221319959/5000000000000 : ℚ) : ℝ) ≤ stT272 129 := by
  have hc : ((-490909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432221319959/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-490909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c130 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((165003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265613/1250000) (δ := 13787/1000000000) (ψ := -29149/31250) 272 211
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t130 : ((144706237949/2500000000000 : ℚ) : ℝ) ≤ stT272 130 := by
  have hc : ((329981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144706237949/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((329981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c131 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((330137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 771467/2500000) (δ := 13787/1000000000) (ψ := -29149/31250) 272 211
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t131 : ((36049791531/1250000000000 : ℚ) : ℝ) ≤ stT272 131 := by
  have hc : ((330087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36049791531/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((330087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c132 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-493517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7450967/10000000) (δ := 13679/1000000000) (ψ := -29149/31250) 272 212
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t132 : ((-214786763919/2500000000000 : ℚ) : ℝ) ≤ stT272 132 := by
  have hc : ((-246771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214786763919/2500000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-246771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c133 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((599797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2318871/10000000) (δ := 13679/1000000000) (ψ := -29149/31250) 272 212
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t133 : ((520046021423/10000000000000 : ℚ) : ℝ) ≤ stT272 133 := by
  have hc : ((599747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520046021423/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((599747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c134 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((55593/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2774771/10000000) (δ := 27279/1000000000) (ψ := -29149/31250) 272 212
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t134 : ((48019614549/1250000000000 : ℚ) : ℝ) ≤ stT272 134 := by
  have hc : ((222347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48019614549/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((222347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c135 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-249989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7830537/10000000) (δ := 13679/1000000000) (ψ := -29149/31250) 272 212
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t135 : ((-430334081989/5000000000000 : ℚ) : ℝ) ≤ stT272 135 := by
  have hc : ((-500003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-430334081989/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-500003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c136 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((6474/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1429479/5000000) (δ := 13631/1000000000) (ψ := -29149/31250) 272 213
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t136 : ((44405866339/1250000000000 : ℚ) : ℝ) ≤ stT272 136 := by
  have hc : ((207143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44405866339/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((207143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c137 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((660647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212279/1000000) (δ := 13631/1000000000) (ψ := -29149/31250) 272 213
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t137 : ((564385671129/10000000000000 : ℚ) : ℝ) ≤ stT272 137 := by
  have hc : ((660597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((564385671129/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((660597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c138 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-237753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3534113/5000000) (δ := 13631/1000000000) (ψ := -29149/31250) 272 213
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t138 : ((-404799092467/5000000000000 : ℚ) : ℝ) ≤ stT272 138 := by
  have hc : ((-475531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404799092467/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-475531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c139 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((39371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3729933/10000000) (δ := 6869/500000000) (ψ := -29149/31250) 272 214
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t139 : ((4171600631/625000000000 : ℚ) : ℝ) ≤ stT272 139 := by
  have hc : ((19673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4171600631/625000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((19673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c140 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((897001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1144647/10000000) (δ := 6869/500000000) (ψ := -29149/31250) 272 214
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t140 : ((379030862727/5000000000000 : ℚ) : ℝ) ≤ stT272 140 := by
  have hc : ((896951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379030862727/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((896951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c141 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-366593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5984479/10000000) (δ := 6869/500000000) (ψ := -29149/31250) 272 214
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t141 : ((-19296755121/312500000000 : ℚ) : ℝ) ≤ stT272 141 := by
  have hc : ((-183309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19296755121/312500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-183309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c142 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-193013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4917789/10000000) (δ := 6879/500000000) (ψ := -29149/31250) 272 215
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t142 : ((-40498503729/1250000000000 : ℚ) : ℝ) ≤ stT272 142 := by
  have hc : ((-96519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40498503729/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-96519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c143 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((998299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145821/10000000) (δ := 6879/500000000) (ψ := -29149/31250) 272 215
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t143 : ((417388870129/5000000000000 : ℚ) : ℝ) ≤ stT272 143 := by
  have hc : ((998249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417388870129/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((998249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c144 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-263197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4592827/10000000) (δ := 6879/500000000) (ψ := -29149/31250) 272 215
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t144 : ((-109686337749/5000000000000 : ℚ) : ℝ) ≤ stT272 144 := by
  have hc : ((-263247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109686337749/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-263247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c145 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-209401/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1602299/2500000) (δ := 13651/1000000000) (ψ := -29149/31250) 272 216
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t145 : ((-69563395257/1000000000000 : ℚ) : ℝ) ≤ stT272 145 := by
  have hc : ((-418827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69563395257/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-418827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c146 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((384267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216953/1250000) (δ := 13651/1000000000) (ψ := -29149/31250) 272 216
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t146 : ((31800060041/500000000000 : ℚ) : ℝ) ≤ stT272 146 := by
  have hc : ((192121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31800060041/500000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((192121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c147 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((198571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 726497/2500000) (δ := 13651/1000000000) (ψ := -29149/31250) 272 216
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t147 : ((40939490289/1250000000000 : ℚ) : ℝ) ≤ stT272 147 := by
  have hc : ((99273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40939490289/1250000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((99273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c148 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-198177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 939523/1250000) (δ := 13651/1000000000) (ψ := -29149/31250) 272 216
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t148 : ((-32581744613/400000000000 : ℚ) : ℝ) ≤ stT272 148 := by
  have hc : ((-198187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32581744613/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-198187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c149 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((125429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3612591/10000000) (δ := 13659/1000000000) (ψ := -29149/31250) 272 217
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t149 : ((102714363549/10000000000000 : ℚ) : ℝ) ≤ stT272 149 := by
  have hc : ((125379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102714363549/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((125379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c150 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((232687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 935861/10000000) (δ := 13659/1000000000) (ψ := -29149/31250) 272 217
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t150 : ((23747224819/312500000000 : ℚ) : ℝ) ≤ stT272 150 := by
  have hc : ((465349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23747224819/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((465349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c151 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-143397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5454189/10000000) (δ := 13659/1000000000) (ψ := -29149/31250) 272 217
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t151 : ((-233410147191/5000000000000 : ℚ) : ℝ) ≤ stT272 151 := by
  have hc : ((-286819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233410147191/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-286819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c152 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-670827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2882649/5000000) (δ := 13767/1000000000) (ψ := -29149/31250) 272 218
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t152 : ((-136038425429/2500000000000 : ℚ) : ℝ) ≤ stT272 152 := by
  have hc : ((-670877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136038425429/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-670877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c153 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((866571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -653133/5000000) (δ := 13767/1000000000) (ψ := -29149/31250) 272 218
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t153 : ((175135158873/2500000000000 : ℚ) : ℝ) ≤ stT272 153 := by
  have hc : ((866521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175135158873/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((866521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c154 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((78951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312373/1000000) (δ := 13767/1000000000) (ψ := -29149/31250) 272 218
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t154 : ((63610379947/2500000000000 : ℚ) : ℝ) ≤ stT272 154 := by
  have hc : ((157877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63610379947/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((157877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c155 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-247839/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 752503/1000000) (δ := 13767/1000000000) (ψ := -29149/31250) 272 218
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t155 : ((-19907928183/250000000000 : ℚ) : ℝ) ≤ stT272 155 := by
  have hc : ((-495703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19907928183/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-495703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c156 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((4681/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1904961/5000000) (δ := 13729/1000000000) (ψ := -29149/31250) 272 219
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t156 : ((1462419/390625000 : ℚ) : ℝ) ≤ stT272 156 := by
  have hc : ((1169/25000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1462419/390625000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((1169/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c157 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((977177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267571/5000000) (δ := 13729/1000000000) (ψ := -29149/31250) 272 219
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t157 : ((389915689461/5000000000000 : ℚ) : ℝ) ≤ stT272 157 := by
  have hc : ((977127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389915689461/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((977127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c158 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-180921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2426299/5000000) (δ := 13729/1000000000) (ψ := -29149/31250) 272 219
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t158 : ((-35988259467/1250000000000 : ℚ) : ℝ) ≤ stT272 158 := by
  have hc : ((-90473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35988259467/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-90473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c159 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-435011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6565109/10000000) (δ := 6811/500000000) (ψ := -29149/31250) 272 220
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t159 : ((-21562885617/312500000000 : ℚ) : ℝ) ≤ stT272 159 := by
  have hc : ((-108759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21562885617/312500000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-108759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c160 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((605253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2301781/10000000) (δ := 6811/500000000) (ψ := -29149/31250) 272 220
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t160 : ((478454730507/10000000000000 : ℚ) : ℝ) ≤ stT272 160 := by
  have hc : ((605203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478454730507/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((605203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c161 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((178783/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1934959/10000000) (δ := 6811/500000000) (ψ := -29149/31250) 272 220
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t161 : ((28178163751/500000000000 : ℚ) : ℝ) ≤ stT272 161 := by
  have hc : ((357541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28178163751/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((357541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c162 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-9693/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6145519/10000000) (δ := 6811/500000000) (ψ := -29149/31250) 272 220
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t162 : ((-2437132423/40000000000 : ℚ) : ℝ) ≤ stT272 162 := by
  have hc : ((-77549/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2437132423/40000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-77549/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c163 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-137073/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42014/78125) (δ := 1711/125000000) (ψ := -29149/31250) 272 221
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t163 : ((-214747451631/5000000000000 : ℚ) : ℝ) ≤ stT272 163 := by
  have hc : ((-274171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214747451631/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-274171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c164 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((441751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -152347/1250000) (δ := 1711/125000000) (ψ := -29149/31250) 272 221
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t164 : ((43116212271/625000000000 : ℚ) : ℝ) ≤ stT272 164 := by
  have hc : ((220863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43116212271/625000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((220863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c165 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((98463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22773/78125) (δ := 1711/125000000) (ψ := -29149/31250) 272 221
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t165 : ((76643517349/2500000000000 : ℚ) : ℝ) ≤ stT272 165 := by
  have hc : ((196901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76643517349/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((196901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c166 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-945357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1755927/2500000) (δ := 1711/125000000) (ψ := -29149/31250) 272 221
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t166 : ((-733778588457/10000000000000 : ℚ) : ℝ) ≤ stT272 166 := by
  have hc : ((-945407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-733778588457/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-945407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c167 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-53201/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4600107/10000000) (δ := 2759/200000000) (ψ := -29149/31250) 272 222
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t167 : ((-643374201/31250000000 : ℚ) : ℝ) ≤ stT272 167 := by
  have hc : ((-53211/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643374201/31250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-53211/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c168 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((39069/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -540439/10000000) (δ := 2759/200000000) (ψ := -29149/31250) 272 222
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t168 : ((7535203893/100000000000 : ℚ) : ℝ) ≤ stT272 168 := by
  have hc : ((39067/40000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7535203893/100000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((39067/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c169 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((171849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139809/400000) (δ := 2759/200000000) (ψ := -29149/31250) 272 222
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t169 : ((13215294477/1000000000000 : ℚ) : ℝ) ≤ stT272 169 := by
  have hc : ((171799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13215294477/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((171799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c170 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-198077/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7507021/10000000) (δ := 2759/200000000) (ψ := -29149/31250) 272 222
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t170 : ((-30385159191/400000000000 : ℚ) : ℝ) ≤ stT272 170 := by
  have hc : ((-198087/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30385159191/400000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-198087/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c171 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-4561/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168507/400000) (δ := 137/10000000) (ψ := -29149/31250) 272 223
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t171 : ((-43617717/5000000000 : ℚ) : ℝ) ≤ stT272 171 := by
  have hc : ((-4563/40000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43617717/5000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-4563/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c172 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((995097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247663/10000000) (δ := 137/10000000) (ψ := -29149/31250) 272 223
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t172 : ((189678844281/2500000000000 : ℚ) : ℝ) ≤ stT272 172 := by
  have hc : ((995047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189678844281/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((995047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c173 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((23229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 738873/2000000) (δ := 137/10000000) (ψ := -29149/31250) 272 223
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t173 : ((7060462681/1000000000000 : ℚ) : ℝ) ≤ stT272 173 := by
  have hc : ((46433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7060462681/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((46433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c174 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-124423/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7613681/10000000) (δ := 137/10000000) (ψ := -29149/31250) 272 223
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t174 : ((-377318759983/5000000000000 : ℚ) : ℝ) ≤ stT272 174 := by
  have hc : ((-497717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377318759983/5000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-497717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c175 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-21591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2098703/5000000) (δ := 1361/100000000) (ψ := -29149/31250) 272 224
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t175 : ((-16328822329/2000000000000 : ℚ) : ℝ) ≤ stT272 175 := by
  have hc : ((-21601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16328822329/2000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-21601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c176 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((991677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161383/5000000) (δ := 1361/100000000) (ψ := -29149/31250) 272 224
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t176 : ((373733308403/5000000000000 : ℚ) : ℝ) ≤ stT272 176 := by
  have hc : ((991627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373733308403/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((991627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c177 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((79069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1764989/5000000) (δ := 1361/100000000) (ψ := -29149/31250) 272 224
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t177 : ((7426638303/625000000000 : ℚ) : ℝ) ≤ stT272 177 := by
  have hc : ((19761/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7426638303/625000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((19761/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c178 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-980617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3680481/5000000) (δ := 1361/100000000) (ψ := -29149/31250) 272 224
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t178 : ((-183760324461/2500000000000 : ℚ) : ℝ) ≤ stT272 178 := by
  have hc : ((-980667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183760324461/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-980667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c179 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-241759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4537437/10000000) (δ := 13717/1000000000) (ψ := -29149/31250) 272 225
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t179 : ((-45184187931/2500000000000 : ℚ) : ℝ) ≤ stT272 179 := by
  have hc : ((-241809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45184187931/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-241809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c180 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((238859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -749157/10000000) (δ := 13717/1000000000) (ψ := -29149/31250) 272 225
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t180 : ((71210173203/1000000000000 : ℚ) : ℝ) ≤ stT272 180 := by
  have hc : ((477693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71210173203/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((477693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c181 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((355571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3018179/10000000) (δ := 13717/1000000000) (ψ := -29149/31250) 272 225
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t181 : ((132128313087/5000000000000 : ℚ) : ℝ) ≤ stT272 181 := by
  have hc : ((355521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132128313087/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((355521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c182 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-906571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6764707/10000000) (δ := 13717/1000000000) (ψ := -29149/31250) 272 225
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t182 : ((-537626253/8000000000 : ℚ) : ℝ) ≤ stT272 182 := by
  have hc : ((-906621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537626253/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-906621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c183 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-493477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5217197/10000000) (δ := 13779/1000000000) (ψ := -29149/31250) 272 226
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t183 : ((-182413007997/5000000000000 : ℚ) : ℝ) ≤ stT272 183 := by
  have hc : ((-493527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182413007997/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-493527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c184 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((822737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1511469/10000000) (δ := 13779/1000000000) (ψ := -29149/31250) 272 226
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t184 : ((606492260583/10000000000000 : ℚ) : ℝ) ≤ stT272 184 := by
  have hc : ((822687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606492260583/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((822687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c185 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((645071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2174199/10000000) (δ := 13779/1000000000) (ψ := -29149/31250) 272 226
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t185 : ((237114234747/5000000000000 : ℚ) : ℝ) ≤ stT272 185 := by
  have hc : ((645021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237114234747/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((645021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c186 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-692667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5839943/10000000) (δ := 13779/1000000000) (ψ := -29149/31250) 272 226
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t186 : ((-126981260553/2500000000000 : ℚ) : ℝ) ≤ stT272 186 := by
  have hc : ((-692717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126981260553/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-692717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c187 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-794357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311093/500000) (δ := 1709/125000000) (ψ := -29149/31250) 272 227
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t187 : ((-580928390111/10000000000000 : ℚ) : ℝ) ≤ stT272 187 := by
  have hc : ((-794407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-580928390111/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-794407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c188 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((50787/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162201/625000) (δ := 1709/125000000) (ψ := -29149/31250) 272 227
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t188 : ((4629566421/125000000000 : ℚ) : ℝ) ≤ stT272 188 := by
  have hc : ((25391/50000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4629566421/125000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((25391/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c189 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((919141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253063/2500000) (δ := 1709/125000000) (ψ := -29149/31250) 272 227
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t189 : ((20891857521/312500000000 : ℚ) : ℝ) ≤ stT272 189 := by
  have hc : ((919091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20891857521/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((919091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c190 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-1331/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150153/2500000) (δ := 1709/125000000) (ψ := -29149/31250) 272 227
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t190 : ((-154526601/8000000000 : ℚ) : ℝ) ≤ stT272 190 := by
  have hc : ((-213/800 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154526601/8000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-213/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c191 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-992011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7537759/10000000) (δ := 6819/500000000) (ψ := -29149/31250) 272 228
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t191 : ((-28713221523/400000000000 : ℚ) : ℝ) ≤ stT272 191 := by
  have hc : ((-992061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28713221523/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-992061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c192 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-5987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3986867/10000000) (δ := 6819/500000000) (ψ := -29149/31250) 272 228
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t192 : ((-1082441789/625000000000 : ℚ) : ℝ) ≤ stT272 192 := by
  have hc : ((-11999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1082441789/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-11999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c193 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((983527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -454403/10000000) (δ := 6819/500000000) (ψ := -29149/31250) 272 228
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t193 : ((141584299351/2000000000000 : ℚ) : ℝ) ≤ stT272 193 := by
  have hc : ((983477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141584299351/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((983477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c194 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((84987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3059837/10000000) (δ := 6819/500000000) (ψ := -29149/31250) 272 228
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t194 : ((61008122071/2500000000000 : ℚ) : ℝ) ≤ stT272 194 := by
  have hc : ((169949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61008122071/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((169949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c195 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-434109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6555989/10000000) (δ := 6819/500000000) (ψ := -29149/31250) 272 228
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t195 : ((-31088986941/500000000000 : ℚ) : ℝ) ≤ stT272 195 := by
  have hc : ((-217067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31088986941/500000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-217067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c196 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-160803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2836853/5000000) (δ := 6873/500000000) (ψ := -29149/31250) 272 229
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t196 : ((-114868260233/2500000000000 : ℚ) : ℝ) ≤ stT272 196 := by
  have hc : ((-321631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114868260233/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-321631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c197 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((316549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1106559/5000000) (δ := 6873/500000000) (ψ := -29149/31250) 272 229
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t197 : ((5637846357/125000000000 : ℚ) : ℝ) ≤ stT272 197 := by
  have hc : ((79131/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5637846357/125000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((79131/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c198 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((220351/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 614963/5000000) (δ := 6873/500000000) (ψ := -29149/31250) 272 229
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t198 : ((313175482913/5000000000000 : ℚ) : ℝ) ≤ stT272 198 := by
  have hc : ((440677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313175482913/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((440677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c199 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-287347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465563/1000000) (δ := 6873/500000000) (ψ := -29149/31250) 272 229
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t199 : ((-101865280077/5000000000000 : ℚ) : ℝ) ≤ stT272 199 := by
  have hc : ((-287397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101865280077/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-287397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c200 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-996469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3821917/5000000) (δ := 11/800000) (ψ := -29149/31250) 272 230
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t200 : ((-704645560533/10000000000000 : ℚ) : ℝ) ≤ stT272 200 := by
  have hc : ((-996519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-704645560533/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-996519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c201 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-129743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2126133/5000000) (δ := 11/800000) (ψ := -29149/31250) 272 230
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t201 : ((-45774486689/5000000000000 : ℚ) : ℝ) ≤ stT272 201 := by
  have hc : ((-129793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45774486689/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-129793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c202 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((939011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87763/1000000) (δ := 11/800000) (ψ := -29149/31250) 272 230
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t202 : ((660650142717/10000000000000 : ℚ) : ℝ) ≤ stT272 202 := by
  have hc : ((938961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((660650142717/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((938961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c203 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((273439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1240207/5000000) (δ := 11/800000) (ψ := -29149/31250) 272 230
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t203 : ((47974724217/1250000000000 : ℚ) : ℝ) ≤ stT272 203 := by
  have hc : ((136707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47974724217/1250000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((136707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c204 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-343727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2910967/5000000) (δ := 11/800000) (ψ := -29149/31250) 272 230
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t204 : ((-30084358629/625000000000 : ℚ) : ℝ) ≤ stT272 204 := by
  have hc : ((-42969/62500 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30084358629/625000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-42969/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c205 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-869177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6560829/10000000) (δ := 13643/1000000000) (ψ := -29149/31250) 272 231
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t205 : ((-607095082837/10000000000000 : ℚ) : ℝ) ≤ stT272 205 := by
  have hc : ((-869227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-607095082837/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-869227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c206 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((667/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3251813/10000000) (δ := 13643/1000000000) (ψ := -29149/31250) 272 231
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t206 : ((743414111/40000000000 : ℚ) : ℝ) ≤ stT272 206 := by
  have hc : ((1067/4000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((743414111/40000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((1067/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c207 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((199973/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8231/2000000) (δ := 13643/1000000000) (ψ := -29149/31250) 272 231
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t207 : ((17372985403/250000000000 : ℚ) : ℝ) ≤ stT272 207 := by
  have hc : ((199963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17372985403/250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((199963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c208 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((120543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3318279/10000000) (δ := 13643/1000000000) (ψ := -29149/31250) 272 231
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t208 : ((334256673/20000000000 : ℚ) : ℝ) ≤ stT272 208 := by
  have hc : ((60259/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334256673/20000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((60259/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c209 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-218221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1315939/2000000) (δ := 13643/1000000000) (ψ := -29149/31250) 272 231
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t209 : ((-60382154181/1000000000000 : ℚ) : ℝ) ≤ stT272 209 := by
  have hc : ((-436467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60382154181/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-436467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c210 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-704823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -735303/1250000) (δ := 13667/1000000000) (ψ := -29149/31250) 272 232
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t210 : ((-243204445809/5000000000000 : ℚ) : ℝ) ≤ stT272 210 := by
  have hc : ((-704873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243204445809/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-704873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c211 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((61021/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165751/625000) (δ := 13667/1000000000) (ψ := -29149/31250) 272 232
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t211 : ((42004262313/1250000000000 : ℚ) : ℝ) ≤ stT272 211 := by
  have hc : ((244059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42004262313/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((244059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c212 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((974741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140773/2500000) (δ := 13667/1000000000) (ψ := -29149/31250) 272 232
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t212 : ((334709864091/5000000000000 : ℚ) : ℝ) ≤ stT272 212 := by
  have hc : ((974691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334709864091/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((974691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c213 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((16377/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117597/312500) (δ := 13667/1000000000) (ψ := -29149/31250) 272 232
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t213 : ((5606379513/1250000000000 : ℚ) : ℝ) ≤ stT272 213 := by
  have hc : ((32729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5606379513/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((32729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c214 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-935073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1737039/2500000) (δ := 13667/1000000000) (ψ := -29149/31250) 272 232
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t214 : ((-319618495539/5000000000000 : ℚ) : ℝ) ≤ stT272 214 := by
  have hc : ((-935123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319618495539/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-935123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c215 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-154277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5589647/10000000) (δ := 6887/500000000) (ψ := -29149/31250) 272 233
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t215 : ((-42089867021/1000000000000 : ℚ) : ℝ) ≤ stT272 215 := by
  have hc : ((-308579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42089867021/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-308579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c216 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((140567/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97367/400000) (δ := 6887/500000000) (ψ := -29149/31250) 272 233
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t216 : ((191270218017/5000000000000 : ℚ) : ℝ) ≤ stT272 216 := by
  have hc : ((281109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191270218017/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((281109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c217 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((480157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 706677/10000000) (δ := 6887/500000000) (ψ := -29149/31250) 272 233
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t217 : ((20370920463/312500000000 : ℚ) : ℝ) ≤ stT272 217 := by
  have hc : ((120033/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20370920463/312500000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((120033/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c218 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((18771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3833113/10000000) (δ := 6887/500000000) (ψ := -29149/31250) 272 233
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t218 : ((1269638461/500000000000 : ℚ) : ℝ) ≤ stT272 218 := by
  have hc : ((9373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1269638461/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((9373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c219 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-934663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6945269/10000000) (δ := 6887/500000000) (ψ := -29149/31250) 272 233
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t219 : ((-315810546597/5000000000000 : ℚ) : ℝ) ≤ stT272 219 := by
  have hc : ((-934713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315810546597/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-934713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c220 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-128093/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5664751/10000000) (δ := 13721/1000000000) (ψ := -29149/31250) 272 234
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t220 : ((-431835213/10000000000 : ℚ) : ℝ) ≤ stT272 220 := by
  have hc : ((-128103/200000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431835213/10000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-128103/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c221 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((512823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -516163/2000000) (δ := 13721/1000000000) (ψ := -29149/31250) 272 234
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t221 : ((10779001233/312500000000 : ℚ) : ℝ) ≤ stT272 221 := by
  have hc : ((512773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10779001233/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((512773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c222 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((490461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489113/10000000) (δ := 13721/1000000000) (ψ := -29149/31250) 272 234
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t222 : ((20572441501/312500000000 : ℚ) : ℝ) ≤ stT272 222 := by
  have hc : ((122609/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20572441501/312500000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((122609/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c223 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((76041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 709061/2000000) (δ := 13721/1000000000) (ψ := -29149/31250) 272 234
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t223 : ((3181502399/312500000000 : ℚ) : ℝ) ≤ stT272 223 := by
  have hc : ((4751/31250 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3181502399/312500000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((4751/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c224 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-874467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6587829/10000000) (δ := 13721/1000000000) (ψ := -29149/31250) 272 234
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t224 : ((-292156015809/5000000000000 : ℚ) : ℝ) ≤ stT272 224 := by
  have hc : ((-874517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292156015809/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-874517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c225 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-190381/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3045571/5000000) (δ := 6807/500000000) (ψ := -29149/31250) 272 235
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t225 : ((-253858126929/5000000000000 : ℚ) : ℝ) ≤ stT272 225 := by
  have hc : ((-380787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253858126929/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-380787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c226 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((333993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48057/156250) (δ := 13607/500000000) (ψ := -29149/31250) 272 235
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t226 : ((22213554417/1000000000000 : ℚ) : ℝ) ≤ stT272 226 := by
  have hc : ((333943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22213554417/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((333943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c227 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((999569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36707/5000000) (δ := 6807/500000000) (ψ := -29149/31250) 272 235
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t227 : ((663403749237/10000000000000 : ℚ) : ℝ) ≤ stT272 227 := by
  have hc : ((999519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((663403749237/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((999519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c228 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((393613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1457797/5000000) (δ := 6807/500000000) (ψ := -29149/31250) 272 235
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t228 : ((130321696879/5000000000000 : ℚ) : ℝ) ≤ stT272 228 := by
  have hc : ((393563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130321696879/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((393563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c229 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-353703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2945773/5000000) (δ := 6807/500000000) (ψ := -29149/31250) 272 235
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t229 : ((-3652346613/78125000000 : ℚ) : ℝ) ≤ stT272 229 := by
  have hc : ((-11054/15625 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3652346613/78125000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-11054/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c230 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-920979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6853453/10000000) (δ := 107/7812500) (ψ := -29149/31250) 272 236
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t230 : ((-607309023049/10000000000000 : ℚ) : ℝ) ≤ stT272 230 := by
  have hc : ((-921029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-607309023049/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-921029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c231 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((473/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3903341/10000000) (δ := 107/7812500) (ψ := -29149/31250) 272 236
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t231 : ((619131891/1000000000000 : ℚ) : ℝ) ≤ stT272 231 := by
  have hc : ((941/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((619131891/1000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((941/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c232 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((92627/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -966013/10000000) (δ := 107/7812500) (ψ := -29149/31250) 272 236
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t232 : ((7601163363/125000000000 : ℚ) : ℝ) ≤ stT272 232 := by
  have hc : ((46311/50000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7601163363/125000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((46311/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c233 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((177113/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391747/2000000) (δ := 107/7812500) (ψ := -29149/31250) 272 236
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t233 : ((232044513321/5000000000000 : ℚ) : ℝ) ≤ stT272 233 := by
  have hc : ((354201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232044513321/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((354201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c234 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-368683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4870971/10000000) (δ := 107/7812500) (ψ := -29149/31250) 272 236
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t234 : ((-241048505493/10000000000000 : ℚ) : ℝ) ≤ stT272 234 := by
  have hc : ((-368733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241048505493/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-368733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c235 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-499723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7770763/10000000) (δ := 107/7812500) (ψ := -29149/31250) 272 236
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t235 : ((-81500028273/1250000000000 : ℚ) : ℝ) ≤ stT272 235 := by
  have hc : ((-124937/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81500028273/1250000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-124937/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c236 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-217073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5049717/10000000) (δ := 69/5000000) (ψ := -29149/31250) 272 237
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t236 : ((-14131885761/500000000000 : ℚ) : ℝ) ≤ stT272 236 := by
  have hc : ((-108549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14131885761/500000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-108549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c237 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((161247/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2174473/10000000) (δ := 69/5000000) (ψ := -29149/31250) 272 237
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t237 : ((209465865861/5000000000000 : ℚ) : ℝ) ≤ stT272 237 := by
  have hc : ((322469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209465865861/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((322469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c238 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((481149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 688667/10000000) (δ := 69/5000000) (ψ := -29149/31250) 272 237
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t238 : ((77966505043/1250000000000 : ℚ) : ℝ) ≤ stT272 238 := by
  have hc : ((120281/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77966505043/1250000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((120281/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c239 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((77121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3539839/10000000) (δ := 69/5000000) (ψ := -29149/31250) 272 237
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t239 : ((3116827451/312500000000 : ℚ) : ℝ) ≤ stT272 239 := by
  have hc : ((9637/62500 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3116827451/312500000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((9637/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c240 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-830969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6379111/10000000) (δ := 69/5000000) (ψ := -29149/31250) 272 237
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t240 : ((-268210551231/5000000000000 : ℚ) : ℝ) ≤ stT272 240 := by
  have hc : ((-831019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268210551231/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-831019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c241 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-42859/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1625353/2500000) (δ := 13693/1000000000) (ψ := -29149/31250) 272 238
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t241 : ((-55219070511/1000000000000 : ℚ) : ℝ) ≤ stT272 241 := by
  have hc : ((-85723/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55219070511/1000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-85723/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c242 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((96379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -921417/2500000) (δ := 13693/1000000000) (ψ := -29149/31250) 272 238
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t242 : ((7740324137/1250000000000 : ℚ) : ℝ) ≤ stT272 242 := by
  have hc : ((96329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7740324137/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((96329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c243 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((938471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55097/625000) (δ := 13693/1000000000) (ψ := -29149/31250) 272 238
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t243 : ((1203994143/20000000000 : ℚ) : ℝ) ≤ stT272 243 := by
  have hc : ((938421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1203994143/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((938421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c244 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((360889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59721/312500) (δ := 13693/1000000000) (ψ := -29149/31250) 272 238
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t244 : ((902419371/19531250000 : ℚ) : ℝ) ≤ stT272 244 := by
  have hc : ((11277/15625 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((902419371/19531250000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((11277/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c245 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-301341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2346119/5000000) (δ := 27293/1000000000) (ψ := -29149/31250) 272 238
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t245 : ((-192551777907/10000000000000 : ℚ) : ℝ) ≤ stT272 245 := by
  have hc : ((-301391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192551777907/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-301391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c246 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-49387/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1865529/2500000) (δ := 13693/1000000000) (ψ := -29149/31250) 272 238
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t246 : ((-62979218483/1000000000000 : ℚ) : ℝ) ≤ stT272 246 := by
  have hc : ((-98779/100000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62979218483/1000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-98779/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c247 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((-584361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5487223/10000000) (δ := 13617/1000000000) (ψ := -29149/31250) 272 239
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t247 : ((-74370390627/2000000000000 : ℚ) : ℝ) ≤ stT272 247 := by
  have hc : ((-584411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74370390627/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-584411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c248 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((228623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2739751/10000000) (δ := 13617/1000000000) (ψ := -29149/31250) 272 239
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t248 : ((14515973/500000000 : ℚ) : ℝ) ≤ stT272 248 := by
  have hc : ((114299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14515973/500000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((114299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c249 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3363/10000000) (δ := 13617/1000000000) (ψ := -29149/31250) 272 239
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t249 : ((158422920019/2500000000000 : ℚ) : ℝ) ≤ stT272 249 := by
  have hc : ((999949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158422920019/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((999949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_c250 :
    |Real.cos (((272 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((231749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 544429/2000000) (δ := 13617/1000000000) (ψ := -29149/31250) 272 239
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st272_t250 : ((7327750121/250000000000 : ℚ) : ℝ) ≤ stT272 250 := by
  have hc : ((57931/125000 : ℚ) : ℝ)
      ≤ Real.cos (((272 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st272_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7327750121/250000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((57931/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st272_p1 : ((595563/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT272 (i+1) := by
  rw [Finset.sum_range_one]
  exact st272_t1

theorem st272_p2 : ((9933663801793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT272 (i+1))
      = (∑ i ∈ Finset.range 1, stT272 (i+1)) + stT272 2 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 1
    simpa using h
  have hprev := st272_p1
  have hstep := st272_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p3 : ((525701245513/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT272 (i+1))
      = (∑ i ∈ Finset.range 2, stT272 (i+1)) + stT272 3 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 2
    simpa using h
  have hprev := st272_p2
  have hstep := st272_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p4 : ((690908433013/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT272 (i+1))
      = (∑ i ∈ Finset.range 3, stT272 (i+1)) + stT272 4 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 3
    simpa using h
  have hprev := st272_p3
  have hstep := st272_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p5 : ((12990329867903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT272 (i+1))
      = (∑ i ∈ Finset.range 4, stT272 (i+1)) + stT272 5 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 4
    simpa using h
  have hprev := st272_p4
  have hstep := st272_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p6 : ((12074049218417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT272 (i+1))
      = (∑ i ∈ Finset.range 5, stT272 (i+1)) + stT272 6 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 5
    simpa using h
  have hprev := st272_p5
  have hstep := st272_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p7 : ((9204641005187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT272 (i+1))
      = (∑ i ∈ Finset.range 6, stT272 (i+1)) + stT272 7 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 6
    simpa using h
  have hprev := st272_p6
  have hstep := st272_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p8 : ((10950770043227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT272 (i+1))
      = (∑ i ∈ Finset.range 7, stT272 (i+1)) + stT272 8 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 7
    simpa using h
  have hprev := st272_p7
  have hstep := st272_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p9 : ((10603086640357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT272 (i+1))
      = (∑ i ∈ Finset.range 8, stT272 (i+1)) + stT272 9 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 8
    simpa using h
  have hprev := st272_p8
  have hstep := st272_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p10 : ((12086061737723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT272 (i+1))
      = (∑ i ∈ Finset.range 9, stT272 (i+1)) + stT272 10 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 9
    simpa using h
  have hprev := st272_p9
  have hstep := st272_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p11 : ((374356640411/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT272 (i+1))
      = (∑ i ∈ Finset.range 10, stT272 (i+1)) + stT272 11 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 10
    simpa using h
  have hprev := st272_p10
  have hstep := st272_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p12 : ((1805091292287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT272 (i+1))
      = (∑ i ∈ Finset.range 11, stT272 (i+1)) + stT272 12 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 11
    simpa using h
  have hprev := st272_p11
  have hstep := st272_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p13 : ((3883589360949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT272 (i+1))
      = (∑ i ∈ Finset.range 12, stT272 (i+1)) + stT272 13 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 12
    simpa using h
  have hprev := st272_p12
  have hstep := st272_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p14 : ((13436636863161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT272 (i+1))
      = (∑ i ∈ Finset.range 13, stT272 (i+1)) + stT272 14 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 13
    simpa using h
  have hprev := st272_p13
  have hstep := st272_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p15 : ((721908289281/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT272 (i+1))
      = (∑ i ∈ Finset.range 14, stT272 (i+1)) + stT272 15 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 14
    simpa using h
  have hprev := st272_p14
  have hstep := st272_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p16 : ((793515945531/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT272 (i+1))
      = (∑ i ∈ Finset.range 15, stT272 (i+1)) + stT272 16 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 15
    simpa using h
  have hprev := st272_p15
  have hstep := st272_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p17 : ((134263091127/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT272 (i+1))
      = (∑ i ∈ Finset.range 16, stT272 (i+1)) + stT272 17 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 16
    simpa using h
  have hprev := st272_p16
  have hstep := st272_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p18 : ((817862169621/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT272 (i+1))
      = (∑ i ∈ Finset.range 17, stT272 (i+1)) + stT272 18 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 17
    simpa using h
  have hprev := st272_p17
  have hstep := st272_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p19 : ((5675963725743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT272 (i+1))
      = (∑ i ∈ Finset.range 18, stT272 (i+1)) + stT272 19 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 18
    simpa using h
  have hprev := st272_p18
  have hstep := st272_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p20 : ((12479609580591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT272 (i+1))
      = (∑ i ∈ Finset.range 19, stT272 (i+1)) + stT272 20 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 19
    simpa using h
  have hprev := st272_p19
  have hstep := st272_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p21 : ((14538509798837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT272 (i+1))
      = (∑ i ∈ Finset.range 20, stT272 (i+1)) + stT272 21 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 20
    simpa using h
  have hprev := st272_p20
  have hstep := st272_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p22 : ((664154298719/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT272 (i+1))
      = (∑ i ∈ Finset.range 21, stT272 (i+1)) + stT272 22 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 21
    simpa using h
  have hprev := st272_p21
  have hstep := st272_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p23 : ((18163103129447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT272 (i+1))
      = (∑ i ∈ Finset.range 22, stT272 (i+1)) + stT272 23 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 22
    simpa using h
  have hprev := st272_p22
  have hstep := st272_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p24 : ((17867327163647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT272 (i+1))
      = (∑ i ∈ Finset.range 23, stT272 (i+1)) + stT272 24 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 23
    simpa using h
  have hprev := st272_p23
  have hstep := st272_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p25 : ((7934310082147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT272 (i+1))
      = (∑ i ∈ Finset.range 24, stT272 (i+1)) + stT272 25 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 24
    simpa using h
  have hprev := st272_p24
  have hstep := st272_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p26 : ((3313672874051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT272 (i+1))
      = (∑ i ∈ Finset.range 25, stT272 (i+1)) + stT272 26 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 25
    simpa using h
  have hprev := st272_p25
  have hstep := st272_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p27 : ((3489918968951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT272 (i+1))
      = (∑ i ∈ Finset.range 26, stT272 (i+1)) + stT272 27 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 26
    simpa using h
  have hprev := st272_p26
  have hstep := st272_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p28 : ((3184020879233/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT272 (i+1))
      = (∑ i ∈ Finset.range 27, stT272 (i+1)) + stT272 28 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 27
    simpa using h
  have hprev := st272_p27
  have hstep := st272_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p29 : ((4385658448123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT272 (i+1))
      = (∑ i ∈ Finset.range 28, stT272 (i+1)) + stT272 29 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 28
    simpa using h
  have hprev := st272_p28
  have hstep := st272_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p30 : ((4039904905389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT272 (i+1))
      = (∑ i ∈ Finset.range 29, stT272 (i+1)) + stT272 30 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 29
    simpa using h
  have hprev := st272_p29
  have hstep := st272_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p31 : ((4195317371479/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT272 (i+1))
      = (∑ i ∈ Finset.range 30, stT272 (i+1)) + stT272 31 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 30
    simpa using h
  have hprev := st272_p30
  have hstep := st272_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p32 : ((2190896409819/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT272 (i+1))
      = (∑ i ∈ Finset.range 31, stT272 (i+1)) + stT272 32 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 31
    simpa using h
  have hprev := st272_p31
  have hstep := st272_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p33 : ((1973988632511/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT272 (i+1))
      = (∑ i ∈ Finset.range 32, stT272 (i+1)) + stT272 33 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 32
    simpa using h
  have hprev := st272_p32
  have hstep := st272_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p34 : ((16373894364793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT272 (i+1))
      = (∑ i ∈ Finset.range 33, stT272 (i+1)) + stT272 34 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 33
    simpa using h
  have hprev := st272_p33
  have hstep := st272_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p35 : ((17945475130873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT272 (i+1))
      = (∑ i ∈ Finset.range 34, stT272 (i+1)) + stT272 35 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 34
    simpa using h
  have hprev := st272_p34
  have hstep := st272_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p36 : ((8819076701371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT272 (i+1))
      = (∑ i ∈ Finset.range 35, stT272 (i+1)) + stT272 36 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 35
    simpa using h
  have hprev := st272_p35
  have hstep := st272_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p37 : ((8016150341381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT272 (i+1))
      = (∑ i ∈ Finset.range 36, stT272 (i+1)) + stT272 37 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 36
    simpa using h
  have hprev := st272_p36
  have hstep := st272_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p38 : ((1856283404269/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT272 (i+1))
      = (∑ i ∈ Finset.range 37, stT272 (i+1)) + stT272 38 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 37
    simpa using h
  have hprev := st272_p37
  have hstep := st272_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p39 : ((3698886255771/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT272 (i+1))
      = (∑ i ∈ Finset.range 38, stT272 (i+1)) + stT272 39 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 38
    simpa using h
  have hprev := st272_p38
  have hstep := st272_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p40 : ((1955941863729/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT272 (i+1))
      = (∑ i ∈ Finset.range 39, stT272 (i+1)) + stT272 40 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 39
    simpa using h
  have hprev := st272_p39
  have hstep := st272_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p41 : ((4240893299511/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT272 (i+1))
      = (∑ i ∈ Finset.range 40, stT272 (i+1)) + stT272 41 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 40
    simpa using h
  have hprev := st272_p40
  have hstep := st272_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p42 : ((3687784828313/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT272 (i+1))
      = (∑ i ∈ Finset.range 41, stT272 (i+1)) + stT272 42 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 41
    simpa using h
  have hprev := st272_p41
  have hstep := st272_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p43 : ((3987839046931/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT272 (i+1))
      = (∑ i ∈ Finset.range 42, stT272 (i+1)) + stT272 43 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 42
    simpa using h
  have hprev := st272_p42
  have hstep := st272_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p44 : ((21413544298643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT272 (i+1))
      = (∑ i ∈ Finset.range 43, stT272 (i+1)) + stT272 44 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 43
    simpa using h
  have hprev := st272_p43
  have hstep := st272_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p45 : ((22797496539667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT272 (i+1))
      = (∑ i ∈ Finset.range 44, stT272 (i+1)) + stT272 45 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 44
    simpa using h
  have hprev := st272_p44
  have hstep := st272_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p46 : ((23938732231723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT272 (i+1))
      = (∑ i ∈ Finset.range 45, stT272 (i+1)) + stT272 46 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 45
    simpa using h
  have hprev := st272_p45
  have hstep := st272_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p47 : ((24575455858607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT272 (i+1))
      = (∑ i ∈ Finset.range 46, stT272 (i+1)) + stT272 47 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 46
    simpa using h
  have hprev := st272_p46
  have hstep := st272_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p48 : ((24424278099743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT272 (i+1))
      = (∑ i ∈ Finset.range 47, stT272 (i+1)) + stT272 48 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 47
    simpa using h
  have hprev := st272_p47
  have hstep := st272_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p49 : ((23419881983699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT272 (i+1))
      = (∑ i ∈ Finset.range 48, stT272 (i+1)) + stT272 49 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 48
    simpa using h
  have hprev := st272_p48
  have hstep := st272_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p50 : ((22005604344069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT272 (i+1))
      = (∑ i ∈ Finset.range 49, stT272 (i+1)) + stT272 50 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 49
    simpa using h
  have hprev := st272_p49
  have hstep := st272_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p51 : ((10564134042743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT272 (i+1))
      = (∑ i ∈ Finset.range 50, stT272 (i+1)) + stT272 51 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 50
    simpa using h
  have hprev := st272_p50
  have hstep := st272_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p52 : ((5392558061059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT272 (i+1))
      = (∑ i ∈ Finset.range 51, stT272 (i+1)) + stT272 52 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 51
    simpa using h
  have hprev := st272_p51
  have hstep := st272_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p53 : ((1433093207101/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT272 (i+1))
      = (∑ i ∈ Finset.range 52, stT272 (i+1)) + stT272 53 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 52
    simpa using h
  have hprev := st272_p52
  have hstep := st272_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p54 : ((23601060798943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT272 (i+1))
      = (∑ i ∈ Finset.range 53, stT272 (i+1)) + stT272 54 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 53
    simpa using h
  have hprev := st272_p53
  have hstep := st272_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p55 : ((22656472888943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT272 (i+1))
      = (∑ i ∈ Finset.range 54, stT272 (i+1)) + stT272 55 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 54
    simpa using h
  have hprev := st272_p54
  have hstep := st272_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p56 : ((861763954831/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT272 (i+1))
      = (∑ i ∈ Finset.range 55, stT272 (i+1)) + stT272 56 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 55
    simpa using h
  have hprev := st272_p55
  have hstep := st272_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p57 : ((22162146694487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT272 (i+1))
      = (∑ i ∈ Finset.range 56, stT272 (i+1)) + stT272 57 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 56
    simpa using h
  have hprev := st272_p56
  have hstep := st272_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p58 : ((23334346501631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT272 (i+1))
      = (∑ i ∈ Finset.range 57, stT272 (i+1)) + stT272 58 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 57
    simpa using h
  have hprev := st272_p57
  have hstep := st272_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p59 : ((22676078370381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT272 (i+1))
      = (∑ i ∈ Finset.range 58, stT272 (i+1)) + stT272 59 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 58
    simpa using h
  have hprev := st272_p58
  have hstep := st272_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p60 : ((10832415183963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT272 (i+1))
      = (∑ i ∈ Finset.range 59, stT272 (i+1)) + stT272 60 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 59
    simpa using h
  have hprev := st272_p59
  have hstep := st272_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p61 : ((11328772885787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT272 (i+1))
      = (∑ i ∈ Finset.range 60, stT272 (i+1)) + stT272 61 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 60
    simpa using h
  have hprev := st272_p60
  have hstep := st272_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p62 : ((23144942945351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT272 (i+1))
      = (∑ i ∈ Finset.range 61, stT272 (i+1)) + stT272 62 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 61
    simpa using h
  have hprev := st272_p61
  have hstep := st272_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p63 : ((21885711044463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT272 (i+1))
      = (∑ i ∈ Finset.range 62, stT272 (i+1)) + stT272 63 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 62
    simpa using h
  have hprev := st272_p62
  have hstep := st272_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p64 : ((22366882294463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT272 (i+1))
      = (∑ i ∈ Finset.range 63, stT272 (i+1)) + stT272 64 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 63
    simpa using h
  have hprev := st272_p63
  have hstep := st272_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p65 : ((23147085364403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT272 (i+1))
      = (∑ i ∈ Finset.range 64, stT272 (i+1)) + stT272 65 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 64
    simpa using h
  have hprev := st272_p64
  have hstep := st272_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p66 : ((10962534324469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT272 (i+1))
      = (∑ i ∈ Finset.range 65, stT272 (i+1)) + stT272 66 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 65
    simpa using h
  have hprev := st272_p65
  have hstep := st272_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p67 : ((1125608479133/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT272 (i+1))
      = (∑ i ∈ Finset.range 66, stT272 (i+1)) + stT272 67 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 66
    simpa using h
  have hprev := st272_p66
  have hstep := st272_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p68 : ((11484760088129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT272 (i+1))
      = (∑ i ∈ Finset.range 67, stT272 (i+1)) + stT272 68 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 67
    simpa using h
  have hprev := st272_p67
  have hstep := st272_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p69 : ((34125879493/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT272 (i+1))
      = (∑ i ∈ Finset.range 68, stT272 (i+1)) + stT272 69 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 68
    simpa using h
  have hprev := st272_p68
  have hstep := st272_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p70 : ((716660174101/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT272 (i+1))
      = (∑ i ∈ Finset.range 69, stT272 (i+1)) + stT272 70 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 69
    simpa using h
  have hprev := st272_p69
  have hstep := st272_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p71 : ((2243100878807/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT272 (i+1))
      = (∑ i ∈ Finset.range 70, stT272 (i+1)) + stT272 71 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 70
    simpa using h
  have hprev := st272_p70
  have hstep := st272_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p72 : ((11083501032683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT272 (i+1))
      = (∑ i ∈ Finset.range 71, stT272 (i+1)) + stT272 72 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 71
    simpa using h
  have hprev := st272_p71
  have hstep := st272_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p73 : ((23035403722159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT272 (i+1))
      = (∑ i ∈ Finset.range 72, stT272 (i+1)) + stT272 73 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 72
    simpa using h
  have hprev := st272_p72
  have hstep := st272_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p74 : ((4378149033923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT272 (i+1))
      = (∑ i ∈ Finset.range 73, stT272 (i+1)) + stT272 74 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 73
    simpa using h
  have hprev := st272_p73
  have hstep := st272_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p75 : ((4596323594483/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT272 (i+1))
      = (∑ i ∈ Finset.range 74, stT272 (i+1)) + stT272 75 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 74
    simpa using h
  have hprev := st272_p74
  have hstep := st272_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p76 : ((11089136906317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT272 (i+1))
      = (∑ i ∈ Finset.range 75, stT272 (i+1)) + stT272 76 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 75
    simpa using h
  have hprev := st272_p75
  have hstep := st272_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p77 : ((22581572044899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT272 (i+1))
      = (∑ i ∈ Finset.range 76, stT272 (i+1)) + stT272 77 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 76
    simpa using h
  have hprev := st272_p76
  have hstep := st272_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p78 : ((4517740625089/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT272 (i+1))
      = (∑ i ∈ Finset.range 77, stT272 (i+1)) + stT272 78 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 77
    simpa using h
  have hprev := st272_p77
  have hstep := st272_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p79 : ((22224321999973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT272 (i+1))
      = (∑ i ∈ Finset.range 78, stT272 (i+1)) + stT272 79 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 78
    simpa using h
  have hprev := st272_p78
  have hstep := st272_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p80 : ((11432194033121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT272 (i+1))
      = (∑ i ∈ Finset.range 79, stT272 (i+1)) + stT272 80 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 79
    simpa using h
  have hprev := st272_p79
  have hstep := st272_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p81 : ((11015914811209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT272 (i+1))
      = (∑ i ∈ Finset.range 80, stT272 (i+1)) + stT272 81 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 80
    simpa using h
  have hprev := st272_p80
  have hstep := st272_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p82 : ((11492852999299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT272 (i+1))
      = (∑ i ∈ Finset.range 81, stT272 (i+1)) + stT272 82 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 81
    simpa using h
  have hprev := st272_p81
  have hstep := st272_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p83 : ((10981654310767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT272 (i+1))
      = (∑ i ∈ Finset.range 82, stT272 (i+1)) + stT272 83 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 82
    simpa using h
  have hprev := st272_p82
  have hstep := st272_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p84 : ((5754651930039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT272 (i+1))
      = (∑ i ∈ Finset.range 83, stT272 (i+1)) + stT272 84 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 83
    simpa using h
  have hprev := st272_p83
  have hstep := st272_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p85 : ((21951282051831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT272 (i+1))
      = (∑ i ∈ Finset.range 84, stT272 (i+1)) + stT272 85 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 84
    simpa using h
  have hprev := st272_p84
  have hstep := st272_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p86 : ((11509536359357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT272 (i+1))
      = (∑ i ∈ Finset.range 85, stT272 (i+1)) + stT272 86 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 85
    simpa using h
  have hprev := st272_p85
  have hstep := st272_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p87 : ((548922240733/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT272 (i+1))
      = (∑ i ∈ Finset.range 86, stT272 (i+1)) + stT272 87 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 86
    simpa using h
  have hprev := st272_p86
  have hstep := st272_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p88 : ((23007551780147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT272 (i+1))
      = (∑ i ∈ Finset.range 87, stT272 (i+1)) + stT272 88 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 87
    simpa using h
  have hprev := st272_p87
  have hstep := st272_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p89 : ((21977302624017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT272 (i+1))
      = (∑ i ∈ Finset.range 88, stT272 (i+1)) + stT272 89 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 88
    simpa using h
  have hprev := st272_p88
  have hstep := st272_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p90 : ((22970949826461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT272 (i+1))
      = (∑ i ∈ Finset.range 89, stT272 (i+1)) + stT272 90 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 89
    simpa using h
  have hprev := st272_p89
  have hstep := st272_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p91 : ((5509807219259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT272 (i+1))
      = (∑ i ∈ Finset.range 90, stT272 (i+1)) + stT272 91 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 90
    simpa using h
  have hprev := st272_p90
  have hstep := st272_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p92 : ((5718063582689/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT272 (i+1))
      = (∑ i ∈ Finset.range 91, stT272 (i+1)) + stT272 92 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 91
    simpa using h
  have hprev := st272_p91
  have hstep := st272_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p93 : ((5546198639733/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT272 (i+1))
      = (∑ i ∈ Finset.range 92, stT272 (i+1)) + stT272 93 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 92
    simpa using h
  have hprev := st272_p92
  have hstep := st272_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p94 : ((4534437066507/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT272 (i+1))
      = (∑ i ∈ Finset.range 93, stT272 (i+1)) + stT272 94 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 93
    simpa using h
  have hprev := st272_p93
  have hstep := st272_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p95 : ((22439263476039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT272 (i+1))
      = (∑ i ∈ Finset.range 94, stT272 (i+1)) + stT272 95 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 94
    simpa using h
  have hprev := st272_p94
  have hstep := st272_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p96 : ((1398343735119/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT272 (i+1))
      = (∑ i ∈ Finset.range 95, stT272 (i+1)) + stT272 96 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 95
    simpa using h
  have hprev := st272_p95
  have hstep := st272_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p97 : ((11378486296573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT272 (i+1))
      = (∑ i ∈ Finset.range 96, stT272 (i+1)) + stT272 97 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 96
    simpa using h
  have hprev := st272_p96
  have hstep := st272_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p98 : ((22076411303833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT272 (i+1))
      = (∑ i ∈ Finset.range 97, stT272 (i+1)) + stT272 98 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 97
    simpa using h
  have hprev := st272_p97
  have hstep := st272_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p99 : ((179536643199/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT272 (i+1))
      = (∑ i ∈ Finset.range 98, stT272 (i+1)) + stT272 99 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 98
    simpa using h
  have hprev := st272_p98
  have hstep := st272_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p100 : ((343462333273/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT272 (i+1))
      = (∑ i ∈ Finset.range 99, stT272 (i+1)) + stT272 100 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 99
    simpa using h
  have hprev := st272_p99
  have hstep := st272_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p101 : ((11450644049027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT272 (i+1))
      = (∑ i ∈ Finset.range 100, stT272 (i+1)) + stT272 101 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 100
    simpa using h
  have hprev := st272_p100
  have hstep := st272_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p102 : ((11125097248699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT272 (i+1))
      = (∑ i ∈ Finset.range 101, stT272 (i+1)) + stT272 102 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 101
    simpa using h
  have hprev := st272_p101
  have hstep := st272_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p103 : ((702324575149/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT272 (i+1))
      = (∑ i ∈ Finset.range 102, stT272 (i+1)) + stT272 103 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 102
    simpa using h
  have hprev := st272_p102
  have hstep := st272_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p104 : ((5687264902577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT272 (i+1))
      = (∑ i ∈ Finset.range 103, stT272 (i+1)) + stT272 104 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 103
    simpa using h
  have hprev := st272_p103
  have hstep := st272_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p105 : ((4406744249921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT272 (i+1))
      = (∑ i ∈ Finset.range 104, stT272 (i+1)) + stT272 105 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 104
    simpa using h
  have hprev := st272_p104
  have hstep := st272_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p106 : ((1149421369297/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT272 (i+1))
      = (∑ i ∈ Finset.range 105, stT272 (i+1)) + stT272 106 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 105
    simpa using h
  have hprev := st272_p105
  have hstep := st272_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p107 : ((22099016778359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT272 (i+1))
      = (∑ i ∈ Finset.range 106, stT272 (i+1)) + stT272 107 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 106
    simpa using h
  have hprev := st272_p106
  have hstep := st272_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p108 : ((22607365755359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT272 (i+1))
      = (∑ i ∈ Finset.range 107, stT272 (i+1)) + stT272 108 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 107
    simpa using h
  have hprev := st272_p107
  have hstep := st272_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p109 : ((4536396271717/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT272 (i+1))
      = (∑ i ∈ Finset.range 108, stT272 (i+1)) + stT272 109 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 108
    simpa using h
  have hprev := st272_p108
  have hstep := st272_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p110 : ((881685637727/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT272 (i+1))
      = (∑ i ∈ Finset.range 109, stT272 (i+1)) + stT272 110 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 109
    simpa using h
  have hprev := st272_p109
  have hstep := st272_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p111 : ((22979843516499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT272 (i+1))
      = (∑ i ∈ Finset.range 110, stT272 (i+1)) + stT272 111 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 110
    simpa using h
  have hprev := st272_p110
  have hstep := st272_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p112 : ((22172728033459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT272 (i+1))
      = (∑ i ∈ Finset.range 111, stT272 (i+1)) + stT272 112 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 111
    simpa using h
  have hprev := st272_p111
  have hstep := st272_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p113 : ((22450747481539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT272 (i+1))
      = (∑ i ∈ Finset.range 112, stT272 (i+1)) + stT272 113 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 112
    simpa using h
  have hprev := st272_p112
  have hstep := st272_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p114 : ((22853893002109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT272 (i+1))
      = (∑ i ∈ Finset.range 113, stT272 (i+1)) + stT272 114 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 113
    simpa using h
  have hprev := st272_p113
  have hstep := st272_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p115 : ((5495257522351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT272 (i+1))
      = (∑ i ∈ Finset.range 114, stT272 (i+1)) + stT272 115 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 114
    simpa using h
  have hprev := st272_p114
  have hstep := st272_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p116 : ((5706534557341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT272 (i+1))
      = (∑ i ∈ Finset.range 115, stT272 (i+1)) + stT272 116 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 115
    simpa using h
  have hprev := st272_p115
  have hstep := st272_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p117 : ((450406007111/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT272 (i+1))
      = (∑ i ∈ Finset.range 116, stT272 (i+1)) + stT272 117 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 116
    simpa using h
  have hprev := st272_p116
  have hstep := st272_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p118 : ((441747152307/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT272 (i+1))
      = (∑ i ∈ Finset.range 117, stT272 (i+1)) + stT272 118 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 117
    simpa using h
  have hprev := st272_p117
  have hstep := st272_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p119 : ((5744704042329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT272 (i+1))
      = (∑ i ∈ Finset.range 118, stT272 (i+1)) + stT272 119 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 118
    simpa using h
  have hprev := st272_p118
  have hstep := st272_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p120 : ((2224137524087/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT272 (i+1))
      = (∑ i ∈ Finset.range 119, stT272 (i+1)) + stT272 120 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 119
    simpa using h
  have hprev := st272_p119
  have hstep := st272_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p121 : ((1114612895863/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT272 (i+1))
      = (∑ i ∈ Finset.range 120, stT272 (i+1)) + stT272 121 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 120
    simpa using h
  have hprev := st272_p120
  have hstep := st272_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p122 : ((11485251246191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT272 (i+1))
      = (∑ i ∈ Finset.range 121, stT272 (i+1)) + stT272 122 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 121
    simpa using h
  have hprev := st272_p121
  have hstep := st272_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p123 : ((11043133591751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT272 (i+1))
      = (∑ i ∈ Finset.range 122, stT272 (i+1)) + stT272 123 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 122
    simpa using h
  have hprev := st272_p122
  have hstep := st272_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p124 : ((5616046090777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT272 (i+1))
      = (∑ i ∈ Finset.range 123, stT272 (i+1)) + stT272 124 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 123
    simpa using h
  have hprev := st272_p123
  have hstep := st272_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p125 : ((22910438142937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT272 (i+1))
      = (∑ i ∈ Finset.range 124, stT272 (i+1)) + stT272 125 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 124
    simpa using h
  have hprev := st272_p124
  have hstep := st272_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p126 : ((2752746227753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT272 (i+1))
      = (∑ i ∈ Finset.range 125, stT272 (i+1)) + stT272 126 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 125
    simpa using h
  have hprev := st272_p125
  have hstep := st272_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p127 : ((1128071495801/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT272 (i+1))
      = (∑ i ∈ Finset.range 126, stT272 (i+1)) + stT272 127 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 126
    simpa using h
  have hprev := st272_p126
  have hstep := st272_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p128 : ((22868378617079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT272 (i+1))
      = (∑ i ∈ Finset.range 127, stT272 (i+1)) + stT272 128 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 127
    simpa using h
  have hprev := st272_p127
  have hstep := st272_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p129 : ((22003935977161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT272 (i+1))
      = (∑ i ∈ Finset.range 128, stT272 (i+1)) + stT272 129 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 128
    simpa using h
  have hprev := st272_p128
  have hstep := st272_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p130 : ((22582760928957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT272 (i+1))
      = (∑ i ∈ Finset.range 129, stT272 (i+1)) + stT272 130 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 129
    simpa using h
  have hprev := st272_p129
  have hstep := st272_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p131 : ((4574231852241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT272 (i+1))
      = (∑ i ∈ Finset.range 130, stT272 (i+1)) + stT272 131 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 130
    simpa using h
  have hprev := st272_p130
  have hstep := st272_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p132 : ((22012012205529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT272 (i+1))
      = (∑ i ∈ Finset.range 131, stT272 (i+1)) + stT272 132 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 131
    simpa using h
  have hprev := st272_p131
  have hstep := st272_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p133 : ((2816507278369/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT272 (i+1))
      = (∑ i ∈ Finset.range 132, stT272 (i+1)) + stT272 133 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 132
    simpa using h
  have hprev := st272_p132
  have hstep := st272_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p134 : ((1432263446459/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT272 (i+1))
      = (∑ i ∈ Finset.range 133, stT272 (i+1)) + stT272 134 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 133
    simpa using h
  have hprev := st272_p133
  have hstep := st272_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p135 : ((11027773489683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT272 (i+1))
      = (∑ i ∈ Finset.range 134, stT272 (i+1)) + stT272 135 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 134
    simpa using h
  have hprev := st272_p134
  have hstep := st272_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p136 : ((11205396955039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT272 (i+1))
      = (∑ i ∈ Finset.range 135, stT272 (i+1)) + stT272 136 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 135
    simpa using h
  have hprev := st272_p135
  have hstep := st272_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p137 : ((22975179581207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT272 (i+1))
      = (∑ i ∈ Finset.range 136, stT272 (i+1)) + stT272 137 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 136
    simpa using h
  have hprev := st272_p136
  have hstep := st272_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p138 : ((22165581396273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT272 (i+1))
      = (∑ i ∈ Finset.range 137, stT272 (i+1)) + stT272 138 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 137
    simpa using h
  have hprev := st272_p137
  have hstep := st272_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p139 : ((22232327006369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT272 (i+1))
      = (∑ i ∈ Finset.range 138, stT272 (i+1)) + stT272 139 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 138
    simpa using h
  have hprev := st272_p138
  have hstep := st272_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p140 : ((22990388731823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT272 (i+1))
      = (∑ i ∈ Finset.range 139, stT272 (i+1)) + stT272 140 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 139
    simpa using h
  have hprev := st272_p139
  have hstep := st272_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p141 : ((22372892567951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT272 (i+1))
      = (∑ i ∈ Finset.range 140, stT272 (i+1)) + stT272 141 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 140
    simpa using h
  have hprev := st272_p140
  have hstep := st272_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p142 : ((22048904538119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT272 (i+1))
      = (∑ i ∈ Finset.range 141, stT272 (i+1)) + stT272 142 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 141
    simpa using h
  have hprev := st272_p141
  have hstep := st272_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p143 : ((22883682278377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT272 (i+1))
      = (∑ i ∈ Finset.range 142, stT272 (i+1)) + stT272 143 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 142
    simpa using h
  have hprev := st272_p142
  have hstep := st272_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p144 : ((22664309602879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT272 (i+1))
      = (∑ i ∈ Finset.range 143, stT272 (i+1)) + stT272 144 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 143
    simpa using h
  have hprev := st272_p143
  have hstep := st272_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p145 : ((21968675650309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT272 (i+1))
      = (∑ i ∈ Finset.range 144, stT272 (i+1)) + stT272 145 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 144
    simpa using h
  have hprev := st272_p144
  have hstep := st272_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p146 : ((22604676851129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT272 (i+1))
      = (∑ i ∈ Finset.range 145, stT272 (i+1)) + stT272 146 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 145
    simpa using h
  have hprev := st272_p145
  have hstep := st272_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p147 : ((22932192773441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT272 (i+1))
      = (∑ i ∈ Finset.range 146, stT272 (i+1)) + stT272 147 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 146
    simpa using h
  have hprev := st272_p146
  have hstep := st272_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p148 : ((5529412289529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT272 (i+1))
      = (∑ i ∈ Finset.range 147, stT272 (i+1)) + stT272 148 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 147
    simpa using h
  have hprev := st272_p147
  have hstep := st272_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p149 : ((4444072704333/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT272 (i+1))
      = (∑ i ∈ Finset.range 148, stT272 (i+1)) + stT272 149 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 148
    simpa using h
  have hprev := st272_p148
  have hstep := st272_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p150 : ((22980274715873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT272 (i+1))
      = (∑ i ∈ Finset.range 149, stT272 (i+1)) + stT272 150 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 149
    simpa using h
  have hprev := st272_p149
  have hstep := st272_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p151 : ((22513454421491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT272 (i+1))
      = (∑ i ∈ Finset.range 150, stT272 (i+1)) + stT272 151 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 150
    simpa using h
  have hprev := st272_p150
  have hstep := st272_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p152 : ((878772028791/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT272 (i+1))
      = (∑ i ∈ Finset.range 151, stT272 (i+1)) + stT272 152 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 151
    simpa using h
  have hprev := st272_p151
  have hstep := st272_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p153 : ((22669841355267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT272 (i+1))
      = (∑ i ∈ Finset.range 152, stT272 (i+1)) + stT272 153 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 152
    simpa using h
  have hprev := st272_p152
  have hstep := st272_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p154 : ((4584856575011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT272 (i+1))
      = (∑ i ∈ Finset.range 153, stT272 (i+1)) + stT272 154 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 153
    simpa using h
  have hprev := st272_p153
  have hstep := st272_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p155 : ((4425593149547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT272 (i+1))
      = (∑ i ∈ Finset.range 154, stT272 (i+1)) + stT272 155 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 154
    simpa using h
  have hprev := st272_p154
  have hstep := st272_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p156 : ((4433080734827/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT272 (i+1))
      = (∑ i ∈ Finset.range 155, stT272 (i+1)) + stT272 156 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 155
    simpa using h
  have hprev := st272_p155
  have hstep := st272_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p157 : ((22945235053057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT272 (i+1))
      = (∑ i ∈ Finset.range 156, stT272 (i+1)) + stT272 157 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 156
    simpa using h
  have hprev := st272_p156
  have hstep := st272_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p158 : ((22657328977321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT272 (i+1))
      = (∑ i ∈ Finset.range 157, stT272 (i+1)) + stT272 158 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 157
    simpa using h
  have hprev := st272_p157
  have hstep := st272_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p159 : ((21967316637577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT272 (i+1))
      = (∑ i ∈ Finset.range 158, stT272 (i+1)) + stT272 159 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 158
    simpa using h
  have hprev := st272_p158
  have hstep := st272_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p160 : ((5611442842021/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT272 (i+1))
      = (∑ i ∈ Finset.range 159, stT272 (i+1)) + stT272 160 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 159
    simpa using h
  have hprev := st272_p159
  have hstep := st272_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p161 : ((719041707597/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT272 (i+1))
      = (∑ i ∈ Finset.range 160, stT272 (i+1)) + stT272 161 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 160
    simpa using h
  have hprev := st272_p160
  have hstep := st272_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p162 : ((11200025768677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT272 (i+1))
      = (∑ i ∈ Finset.range 161, stT272 (i+1)) + stT272 162 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 161
    simpa using h
  have hprev := st272_p161
  have hstep := st272_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p163 : ((5492639158523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT272 (i+1))
      = (∑ i ∈ Finset.range 162, stT272 (i+1)) + stT272 163 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 162
    simpa using h
  have hprev := st272_p162
  have hstep := st272_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p164 : ((5665104007607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT272 (i+1))
      = (∑ i ∈ Finset.range 163, stT272 (i+1)) + stT272 164 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 163
    simpa using h
  have hprev := st272_p163
  have hstep := st272_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p165 : ((1435436881239/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT272 (i+1))
      = (∑ i ∈ Finset.range 164, stT272 (i+1)) + stT272 165 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 164
    simpa using h
  have hprev := st272_p164
  have hstep := st272_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p166 : ((22233211511367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT272 (i+1))
      = (∑ i ∈ Finset.range 165, stT272 (i+1)) + stT272 166 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 165
    simpa using h
  have hprev := st272_p165
  have hstep := st272_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p167 : ((22027331767047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT272 (i+1))
      = (∑ i ∈ Finset.range 166, stT272 (i+1)) + stT272 167 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 166
    simpa using h
  have hprev := st272_p166
  have hstep := st272_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p168 : ((22780852156347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT272 (i+1))
      = (∑ i ∈ Finset.range 167, stT272 (i+1)) + stT272 168 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 167
    simpa using h
  have hprev := st272_p167
  have hstep := st272_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p169 : ((22913005101117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT272 (i+1))
      = (∑ i ∈ Finset.range 168, stT272 (i+1)) + stT272 169 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 168
    simpa using h
  have hprev := st272_p168
  have hstep := st272_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p170 : ((11076688060671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT272 (i+1))
      = (∑ i ∈ Finset.range 169, stT272 (i+1)) + stT272 170 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 169
    simpa using h
  have hprev := st272_p169
  have hstep := st272_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p171 : ((11033070343671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT272 (i+1))
      = (∑ i ∈ Finset.range 170, stT272 (i+1)) + stT272 171 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 170
    simpa using h
  have hprev := st272_p170
  have hstep := st272_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p172 : ((11412428032233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT272 (i+1))
      = (∑ i ∈ Finset.range 171, stT272 (i+1)) + stT272 172 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 171
    simpa using h
  have hprev := st272_p171
  have hstep := st272_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p173 : ((5723865172819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT272 (i+1))
      = (∑ i ∈ Finset.range 172, stT272 (i+1)) + stT272 173 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 172
    simpa using h
  have hprev := st272_p172
  have hstep := st272_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p174 : ((2214082317131/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT272 (i+1))
      = (∑ i ∈ Finset.range 173, stT272 (i+1)) + stT272 174 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 173
    simpa using h
  have hprev := st272_p173
  have hstep := st272_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p175 : ((4411835811933/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT272 (i+1))
      = (∑ i ∈ Finset.range 174, stT272 (i+1)) + stT272 175 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 174
    simpa using h
  have hprev := st272_p174
  have hstep := st272_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p176 : ((22806645676471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT272 (i+1))
      = (∑ i ∈ Finset.range 175, stT272 (i+1)) + stT272 176 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 175
    simpa using h
  have hprev := st272_p175
  have hstep := st272_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p177 : ((22925471889319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT272 (i+1))
      = (∑ i ∈ Finset.range 176, stT272 (i+1)) + stT272 177 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 176
    simpa using h
  have hprev := st272_p176
  have hstep := st272_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p178 : ((887617223659/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT272 (i+1))
      = (∑ i ∈ Finset.range 177, stT272 (i+1)) + stT272 178 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 177
    simpa using h
  have hprev := st272_p177
  have hstep := st272_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p179 : ((22009693839751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT272 (i+1))
      = (∑ i ∈ Finset.range 178, stT272 (i+1)) + stT272 179 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 178
    simpa using h
  have hprev := st272_p178
  have hstep := st272_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p180 : ((22721795571781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT272 (i+1))
      = (∑ i ∈ Finset.range 179, stT272 (i+1)) + stT272 180 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 179
    simpa using h
  have hprev := st272_p179
  have hstep := st272_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p181 : ((4597210439591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT272 (i+1))
      = (∑ i ∈ Finset.range 180, stT272 (i+1)) + stT272 181 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 180
    simpa using h
  have hprev := st272_p180
  have hstep := st272_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p182 : ((4462803876341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT272 (i+1))
      = (∑ i ∈ Finset.range 181, stT272 (i+1)) + stT272 182 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 181
    simpa using h
  have hprev := st272_p181
  have hstep := st272_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p183 : ((21949193365711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT272 (i+1))
      = (∑ i ∈ Finset.range 182, stT272 (i+1)) + stT272 183 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 182
    simpa using h
  have hprev := st272_p182
  have hstep := st272_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p184 : ((11277842813147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT272 (i+1))
      = (∑ i ∈ Finset.range 183, stT272 (i+1)) + stT272 184 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 183
    simpa using h
  have hprev := st272_p183
  have hstep := st272_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p185 : ((5757478523947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT272 (i+1))
      = (∑ i ∈ Finset.range 184, stT272 (i+1)) + stT272 185 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 184
    simpa using h
  have hprev := st272_p184
  have hstep := st272_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p186 : ((2815248631697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT272 (i+1))
      = (∑ i ∈ Finset.range 185, stT272 (i+1)) + stT272 186 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 185
    simpa using h
  have hprev := st272_p185
  have hstep := st272_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p187 : ((4388212132693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT272 (i+1))
      = (∑ i ∈ Finset.range 186, stT272 (i+1)) + stT272 187 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 186
    simpa using h
  have hprev := st272_p186
  have hstep := st272_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p188 : ((4462285195429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT272 (i+1))
      = (∑ i ∈ Finset.range 187, stT272 (i+1)) + stT272 188 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 187
    simpa using h
  have hprev := st272_p187
  have hstep := st272_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p189 : ((22979965417817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT272 (i+1))
      = (∑ i ∈ Finset.range 188, stT272 (i+1)) + stT272 189 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 188
    simpa using h
  have hprev := st272_p188
  have hstep := st272_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p190 : ((22786807166567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT272 (i+1))
      = (∑ i ∈ Finset.range 189, stT272 (i+1)) + stT272 190 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 189
    simpa using h
  have hprev := st272_p189
  have hstep := st272_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p191 : ((5517244157123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT272 (i+1))
      = (∑ i ∈ Finset.range 190, stT272 (i+1)) + stT272 191 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 190
    simpa using h
  have hprev := st272_p190
  have hstep := st272_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p192 : ((5512914389967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT272 (i+1))
      = (∑ i ∈ Finset.range 191, stT272 (i+1)) + stT272 192 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 191
    simpa using h
  have hprev := st272_p191
  have hstep := st272_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p193 : ((22759579056623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT272 (i+1))
      = (∑ i ∈ Finset.range 192, stT272 (i+1)) + stT272 193 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 192
    simpa using h
  have hprev := st272_p192
  have hstep := st272_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p194 : ((23003611544907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT272 (i+1))
      = (∑ i ∈ Finset.range 193, stT272 (i+1)) + stT272 194 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 193
    simpa using h
  have hprev := st272_p193
  have hstep := st272_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p195 : ((22381831806087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT272 (i+1))
      = (∑ i ∈ Finset.range 194, stT272 (i+1)) + stT272 195 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 194
    simpa using h
  have hprev := st272_p194
  have hstep := st272_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p196 : ((4384471753031/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT272 (i+1))
      = (∑ i ∈ Finset.range 195, stT272 (i+1)) + stT272 196 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 195
    simpa using h
  have hprev := st272_p195
  have hstep := st272_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p197 : ((4474677294743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT272 (i+1))
      = (∑ i ∈ Finset.range 196, stT272 (i+1)) + stT272 197 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 196
    simpa using h
  have hprev := st272_p196
  have hstep := st272_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p198 : ((22999737439541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT272 (i+1))
      = (∑ i ∈ Finset.range 197, stT272 (i+1)) + stT272 198 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 197
    simpa using h
  have hprev := st272_p197
  have hstep := st272_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p199 : ((22796006879387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT272 (i+1))
      = (∑ i ∈ Finset.range 198, stT272 (i+1)) + stT272 199 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 198
    simpa using h
  have hprev := st272_p198
  have hstep := st272_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p200 : ((11045680659427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT272 (i+1))
      = (∑ i ∈ Finset.range 199, stT272 (i+1)) + stT272 200 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 199
    simpa using h
  have hprev := st272_p199
  have hstep := st272_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p201 : ((5499953086369/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT272 (i+1))
      = (∑ i ∈ Finset.range 200, stT272 (i+1)) + stT272 201 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 200
    simpa using h
  have hprev := st272_p200
  have hstep := st272_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p202 : ((22660462488193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT272 (i+1))
      = (∑ i ∈ Finset.range 201, stT272 (i+1)) + stT272 202 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 201
    simpa using h
  have hprev := st272_p201
  have hstep := st272_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p203 : ((23044260281929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT272 (i+1))
      = (∑ i ∈ Finset.range 202, stT272 (i+1)) + stT272 203 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 202
    simpa using h
  have hprev := st272_p202
  have hstep := st272_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p204 : ((4512582108773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT272 (i+1))
      = (∑ i ∈ Finset.range 203, stT272 (i+1)) + stT272 204 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 203
    simpa using h
  have hprev := st272_p203
  have hstep := st272_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p205 : ((5488953865257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT272 (i+1))
      = (∑ i ∈ Finset.range 204, stT272 (i+1)) + stT272 205 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 204
    simpa using h
  have hprev := st272_p204
  have hstep := st272_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p206 : ((11070834494389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT272 (i+1))
      = (∑ i ∈ Finset.range 205, stT272 (i+1)) + stT272 206 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 205
    simpa using h
  have hprev := st272_p205
  have hstep := st272_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p207 : ((11418294202449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT272 (i+1))
      = (∑ i ∈ Finset.range 206, stT272 (i+1)) + stT272 207 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 206
    simpa using h
  have hprev := st272_p206
  have hstep := st272_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p208 : ((11501858370699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT272 (i+1))
      = (∑ i ∈ Finset.range 207, stT272 (i+1)) + stT272 208 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 207
    simpa using h
  have hprev := st272_p207
  have hstep := st272_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p209 : ((5599973799897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT272 (i+1))
      = (∑ i ∈ Finset.range 208, stT272 (i+1)) + stT272 209 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 208
    simpa using h
  have hprev := st272_p208
  have hstep := st272_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p210 : ((2191348630797/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT272 (i+1))
      = (∑ i ∈ Finset.range 209, stT272 (i+1)) + stT272 210 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 209
    simpa using h
  have hprev := st272_p209
  have hstep := st272_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p211 : ((11124760203237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT272 (i+1))
      = (∑ i ∈ Finset.range 210, stT272 (i+1)) + stT272 211 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 210
    simpa using h
  have hprev := st272_p210
  have hstep := st272_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p212 : ((89527109901/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT272 (i+1))
      = (∑ i ∈ Finset.range 211, stT272 (i+1)) + stT272 212 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 211
    simpa using h
  have hprev := st272_p211
  have hstep := st272_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p213 : ((574094779269/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT272 (i+1))
      = (∑ i ∈ Finset.range 212, stT272 (i+1)) + stT272 213 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 212
    simpa using h
  have hprev := st272_p212
  have hstep := st272_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p214 : ((11162277089841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT272 (i+1))
      = (∑ i ∈ Finset.range 213, stT272 (i+1)) + stT272 214 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 213
    simpa using h
  have hprev := st272_p213
  have hstep := st272_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p215 : ((684489234671/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT272 (i+1))
      = (∑ i ∈ Finset.range 214, stT272 (i+1)) + stT272 215 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 214
    simpa using h
  have hprev := st272_p214
  have hstep := st272_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p216 : ((11143097972753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT272 (i+1))
      = (∑ i ∈ Finset.range 215, stT272 (i+1)) + stT272 216 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 215
    simpa using h
  have hprev := st272_p215
  have hstep := st272_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p217 : ((11469032700161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT272 (i+1))
      = (∑ i ∈ Finset.range 216, stT272 (i+1)) + stT272 217 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 216
    simpa using h
  have hprev := st272_p216
  have hstep := st272_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p218 : ((11481729084771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT272 (i+1))
      = (∑ i ∈ Finset.range 217, stT272 (i+1)) + stT272 218 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 217
    simpa using h
  have hprev := st272_p217
  have hstep := st272_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p219 : ((5582959269087/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT272 (i+1))
      = (∑ i ∈ Finset.range 218, stT272 (i+1)) + stT272 219 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 218
    simpa using h
  have hprev := st272_p218
  have hstep := st272_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p220 : ((5475000465837/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT272 (i+1))
      = (∑ i ∈ Finset.range 219, stT272 (i+1)) + stT272 220 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 219
    simpa using h
  have hprev := st272_p219
  have hstep := st272_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p221 : ((5561232475701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT272 (i+1))
      = (∑ i ∈ Finset.range 220, stT272 (i+1)) + stT272 221 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 220
    simpa using h
  have hprev := st272_p220
  have hstep := st272_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p222 : ((5725812007709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT272 (i+1))
      = (∑ i ∈ Finset.range 221, stT272 (i+1)) + stT272 222 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 221
    simpa using h
  have hprev := st272_p221
  have hstep := st272_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p223 : ((5751264026901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT272 (i+1))
      = (∑ i ∈ Finset.range 222, stT272 (i+1)) + stT272 223 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 222
    simpa using h
  have hprev := st272_p222
  have hstep := st272_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p224 : ((11210372037993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT272 (i+1))
      = (∑ i ∈ Finset.range 223, stT272 (i+1)) + stT272 224 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 223
    simpa using h
  have hprev := st272_p223
  have hstep := st272_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p225 : ((1369564238883/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT272 (i+1))
      = (∑ i ∈ Finset.range 224, stT272 (i+1)) + stT272 225 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 224
    simpa using h
  have hprev := st272_p224
  have hstep := st272_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p226 : ((11067581683149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT272 (i+1))
      = (∑ i ∈ Finset.range 225, stT272 (i+1)) + stT272 226 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 225
    simpa using h
  have hprev := st272_p225
  have hstep := st272_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p227 : ((4559713423107/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT272 (i+1))
      = (∑ i ∈ Finset.range 226, stT272 (i+1)) + stT272 227 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 226
    simpa using h
  have hprev := st272_p226
  have hstep := st272_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p228 : ((23059210509293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT272 (i+1))
      = (∑ i ∈ Finset.range 227, stT272 (i+1)) + stT272 228 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 227
    simpa using h
  have hprev := st272_p227
  have hstep := st272_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p229 : ((22591710142829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT272 (i+1))
      = (∑ i ∈ Finset.range 228, stT272 (i+1)) + stT272 229 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 228
    simpa using h
  have hprev := st272_p228
  have hstep := st272_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p230 : ((1099220055989/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT272 (i+1))
      = (∑ i ∈ Finset.range 229, stT272 (i+1)) + stT272 230 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 229
    simpa using h
  have hprev := st272_p229
  have hstep := st272_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p231 : ((2199059243869/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT272 (i+1))
      = (∑ i ∈ Finset.range 230, stT272 (i+1)) + stT272 231 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 230
    simpa using h
  have hprev := st272_p230
  have hstep := st272_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p232 : ((2259868550773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT272 (i+1))
      = (∑ i ∈ Finset.range 231, stT272 (i+1)) + stT272 232 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 231
    simpa using h
  have hprev := st272_p231
  have hstep := st272_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p233 : ((5765693633593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT272 (i+1))
      = (∑ i ∈ Finset.range 232, stT272 (i+1)) + stT272 233 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 232
    simpa using h
  have hprev := st272_p232
  have hstep := st272_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p234 : ((22821726028879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT272 (i+1))
      = (∑ i ∈ Finset.range 233, stT272 (i+1)) + stT272 234 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 233
    simpa using h
  have hprev := st272_p233
  have hstep := st272_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p235 : ((4433945160539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT272 (i+1))
      = (∑ i ∈ Finset.range 234, stT272 (i+1)) + stT272 235 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 234
    simpa using h
  have hprev := st272_p234
  have hstep := st272_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p236 : ((875483523499/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT272 (i+1))
      = (∑ i ∈ Finset.range 235, stT272 (i+1)) + stT272 236 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 235
    simpa using h
  have hprev := st272_p235
  have hstep := st272_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p237 : ((22306019819197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT272 (i+1))
      = (∑ i ∈ Finset.range 236, stT272 (i+1)) + stT272 237 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 236
    simpa using h
  have hprev := st272_p236
  have hstep := st272_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p238 : ((22929751859541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT272 (i+1))
      = (∑ i ∈ Finset.range 237, stT272 (i+1)) + stT272 238 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 237
    simpa using h
  have hprev := st272_p237
  have hstep := st272_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p239 : ((23029490337973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT272 (i+1))
      = (∑ i ∈ Finset.range 238, stT272 (i+1)) + stT272 239 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 238
    simpa using h
  have hprev := st272_p238
  have hstep := st272_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p240 : ((22493069235511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT272 (i+1))
      = (∑ i ∈ Finset.range 239, stT272 (i+1)) + stT272 240 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 239
    simpa using h
  have hprev := st272_p239
  have hstep := st272_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p241 : ((21940878530401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT272 (i+1))
      = (∑ i ∈ Finset.range 240, stT272 (i+1)) + stT272 241 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 240
    simpa using h
  have hprev := st272_p240
  have hstep := st272_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p242 : ((22002801123497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT272 (i+1))
      = (∑ i ∈ Finset.range 241, stT272 (i+1)) + stT272 242 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 241
    simpa using h
  have hprev := st272_p241
  have hstep := st272_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p243 : ((22604798194997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT272 (i+1))
      = (∑ i ∈ Finset.range 242, stT272 (i+1)) + stT272 243 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 242
    simpa using h
  have hprev := st272_p242
  have hstep := st272_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p244 : ((23066836912949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT272 (i+1))
      = (∑ i ∈ Finset.range 243, stT272 (i+1)) + stT272 244 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 243
    simpa using h
  have hprev := st272_p243
  have hstep := st272_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p245 : ((11437142567521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT272 (i+1))
      = (∑ i ∈ Finset.range 244, stT272 (i+1)) + stT272 245 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 244
    simpa using h
  have hprev := st272_p244
  have hstep := st272_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p246 : ((5561123237553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT272 (i+1))
      = (∑ i ∈ Finset.range 245, stT272 (i+1)) + stT272 246 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 245
    simpa using h
  have hprev := st272_p245
  have hstep := st272_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p247 : ((21872640997077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT272 (i+1))
      = (∑ i ∈ Finset.range 246, stT272 (i+1)) + stT272 247 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 246
    simpa using h
  have hprev := st272_p246
  have hstep := st272_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p248 : ((22162960457077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT272 (i+1))
      = (∑ i ∈ Finset.range 247, stT272 (i+1)) + stT272 248 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 247
    simpa using h
  have hprev := st272_p247
  have hstep := st272_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p249 : ((22796652137153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT272 (i+1))
      = (∑ i ∈ Finset.range 248, stT272 (i+1)) + stT272 249 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 248
    simpa using h
  have hprev := st272_p248
  have hstep := st272_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_p250 : ((23089762141993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT272 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT272 (i+1))
      = (∑ i ∈ Finset.range 249, stT272 (i+1)) + stT272 250 := by
    have h := Finset.sum_range_succ (fun i => stT272 (i+1)) 249
    simpa using h
  have hprev := st272_p249
  have hstep := st272_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st272_s250 :
    |Real.sin (((272 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))
      - ((443049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 544429/2000000) (δ := 13617/1000000000) (ψ := -29149/31250) 272 239
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 272`** (evaluated boundary). -/
theorem station_272_sign : 0 < hardyG ((((272:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 272 250 (by norm_num) (by norm_num)
    ((-29149/31250 : ℚ) : ℝ)
  have hchain := st272_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT272 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((272 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-29149/31250 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st272_c250
  have hsinb := abs_le.mp st272_s250
  have hbdy_lo : ((-1907361041971/36992125000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((272 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29149/31250 : ℚ) : ℝ))) / 2
          - ((((272:ℕ)):ℝ))
            * Real.sin (((272 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29149/31250 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((272:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((272:ℝ) * Real.log (250:ℝ) - ((-29149/31250 : ℚ) : ℝ))) / 2
        - ((272:ℝ)) * Real.sin ((272:ℝ) * Real.log (250:ℝ) - ((-29149/31250 : ℚ) : ℝ))
        ≥ ((-24126403/100000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((272:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-24126403/100000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-24126403/100000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-24126403/100000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((272:ℕ)):ℝ))+1) * (((((272:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((505640745357/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((23089762141993/10000000000000 : ℚ) : ℝ) + ((-1907361041971/36992125000000 : ℚ) : ℝ)
      - ((505640745357/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-29149/31250 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((272:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-29149/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((272:ℕ)):ℝ)))).re
      - Real.sin ((-29149/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((272:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((272:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((272:ℕ)):ℝ))
      = (((((272:ℕ)):ℝ)) * (Real.log ((((272:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((272:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_272
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
  have hθwin : |(((-29149/31250 : ℚ) : ℝ) + ((60:ℤ)) * (2*Real.pi)) - theta ((((272:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((272:ℕ)):ℝ)))
    (φ := ((-29149/31250 : ℚ) : ℝ) + ((60:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-29149/31250 : ℚ)) : ℝ) 60).1,
    (cos_sin_shift (((-29149/31250 : ℚ)) : ℝ) 60).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_272_sign
end AxiomAudit
