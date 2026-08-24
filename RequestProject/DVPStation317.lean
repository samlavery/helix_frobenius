import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 317` (rung-335.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT317 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((317 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((394423/500000 : ℚ) : ℝ))

theorem st317_c1 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((140933/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -394423/2000000) (δ := 1/1000000000) (ψ := 394423/500000) 317 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t1 : ((140913/200000 : ℚ) : ℝ) ≤ stT317 1 := by
  have hc : ((140913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140913/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((140913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c2 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((563083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2431713/10000000) (δ := 15853/1000000000) (ψ := 394423/500000) 317 35
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t2 : ((3980890512861/10000000000000 : ℚ) : ℝ) ≤ stT317 2 := by
  have hc : ((562983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3980890512861/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((562983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c3 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-63909/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4740113/10000000) (δ := 16007/1000000000) (ψ := 394423/500000) 317 55
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t3 : ((-369094273287/2000000000000 : ℚ) : ℝ) ≤ stT317 3 := by
  have hc : ((-63929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369094273287/2000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-63929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c4 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((201269/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2891271/10000000) (δ := 4001/250000000) (ψ := 394423/500000) 317 70
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t4 : ((201219/1000000 : ℚ) : ℝ) ≤ stT317 4 := by
  have hc : ((201219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201219/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((201219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c5 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((893833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290609/2500000) (δ := 15983/1000000000) (ψ := 394423/500000) 317 81
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t5 : ((799378925991/2000000000000 : ℚ) : ℝ) ≤ stT317 5 := by
  have hc : ((893733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799378925991/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((893733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c6 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-28191/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 856111/2000000) (δ := 3171/200000000) (ψ := 394423/500000) 317 90
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t6 : ((-115170927913/2000000000000 : ℚ) : ℝ) ≤ stT317 6 := by
  have hc : ((-28211/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115170927913/2000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-28211/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c7 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((237891/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 781279/10000000) (δ := 3201/200000000) (ψ := 394423/500000) 317 98
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t7 : ((112381099963/312500000000 : ℚ) : ℝ) ≤ stT317 7 := by
  have hc : ((118933/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112381099963/312500000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((118933/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c8 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((22843/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335083/1000000) (δ := 3987/250000000) (ψ := 394423/500000) 317 105
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t8 : ((80726824989/1000000000000 : ℚ) : ℝ) ≤ stT317 8 := by
  have hc : ((22833/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80726824989/1000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((22833/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c9 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-65529/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2127791/5000000) (δ := 3181/200000000) (ψ := 394423/500000) 317 111
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t9 : ((-109298355193/2500000000000 : ℚ) : ℝ) ≤ stT317 9 := by
  have hc : ((-65579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109298355193/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-65579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c10 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((480373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 351399/5000000) (δ := 15869/1000000000) (ψ := 394423/500000) 317 116
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t10 : ((1518914375471/5000000000000 : ℚ) : ℝ) ≤ stT317 10 := by
  have hc : ((480323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1518914375471/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((480323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c11 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((604647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460737/2000000) (δ := 15933/1000000000) (ψ := 394423/500000) 317 121
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t11 : ((1822777518811/10000000000000 : ℚ) : ℝ) ≤ stT317 11 := by
  have hc : ((604547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1822777518811/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((604547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c12 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((8477/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3820997/10000000) (δ := 15999/1000000000) (ψ := 394423/500000) 317 125
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t12 : ((24413253207/2000000000000 : ℚ) : ℝ) ≤ stT317 12 := by
  have hc : ((8457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24413253207/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((8457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c13 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-98549/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4422983/10000000) (δ := 639/40000000) (ψ := 394423/500000) 317 129
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t13 : ((-273464425099/5000000000000 : ℚ) : ℝ) ≤ stT317 13 := by
  have hc : ((-98599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273464425099/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-98599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c14 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((991731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8043/250000) (δ := 15947/1000000000) (ψ := 394423/500000) 317 133
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t14 : ((662561227543/2500000000000 : ℚ) : ℝ) ≤ stT317 14 := by
  have hc : ((991631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((662561227543/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((991631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c15 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-499983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -391663/500000) (δ := 8009/500000000) (ψ := 394423/500000) 317 137
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t15 : ((-1291079705637/5000000000000 : ℚ) : ℝ) ≤ stT317 15 := by
  have hc : ((-500033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1291079705637/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-500033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c16 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((1457/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -952597/2500000) (δ := 15907/1000000000) (ψ := 394423/500000) 317 140
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t16 : ((11631/1000000 : ℚ) : ℝ) ≤ stT317 16 := by
  have hc : ((11631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11631/1000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((11631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c17 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((201633/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1444641/5000000) (δ := 4007/250000000) (ψ := 394423/500000) 317 143
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t17 : ((122227634637/1250000000000 : ℚ) : ℝ) ≤ stT317 17 := by
  have hc : ((201583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122227634637/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((201583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c18 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-310063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235757/500000) (δ := 319/20000000) (ψ := 394423/500000) 317 146
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t18 : ((-731061324749/10000000000000 : ℚ) : ℝ) ≤ stT317 18 := by
  have hc : ((-310163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731061324749/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-310163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c19 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-179677/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6717189/10000000) (δ := 15939/1000000000) (ψ := 394423/500000) 317 148
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t19 : ((-206126655063/1000000000000 : ℚ) : ℝ) ≤ stT317 19 := by
  have hc : ((-179697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206126655063/1000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-179697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c20 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((99527/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6081/250000) (δ := 7993/500000000) (ψ := 394423/500000) 317 151
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t20 : ((222526679639/1000000000000 : ℚ) : ℝ) ≤ stT317 20 := by
  have hc : ((99517/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222526679639/1000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((99517/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c21 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-7917/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7493547/10000000) (δ := 1/62500) (ψ := 394423/500000) 317 153
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t21 : ((-86390284431/400000000000 : ℚ) : ℝ) ≤ stT317 21 := by
  have hc : ((-39589/40000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86390284431/400000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-39589/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c22 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((448869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2763243/10000000) (δ := 7961/500000000) (ψ := 394423/500000) 317 156
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t22 : ((956778649383/10000000000000 : ℚ) : ℝ) ≤ stT317 22 := by
  have hc : ((448769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((956778649383/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((448769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c23 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((913271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 524441/5000000) (δ := 249/15625000) (ψ := 394423/500000) 317 158
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t23 : ((238011628953/1250000000000 : ℚ) : ℝ) ≤ stT317 23 := by
  have hc : ((913171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238011628953/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((913171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c24 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((224297/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1680719/5000000) (δ := 15953/1000000000) (ψ := 394423/500000) 317 160
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t24 : ((457640108477/10000000000000 : ℚ) : ℝ) ≤ stT317 24 := by
  have hc : ((224197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((457640108477/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((224197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c25 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-147443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4296947/10000000) (δ := 3193/200000000) (ψ := 394423/500000) 317 162
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t25 : ((-295086147543/10000000000000 : ℚ) : ℝ) ≤ stT317 25 := by
  have hc : ((-147543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295086147543/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-147543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c26 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-14573/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158537/400000) (δ := 15879/1000000000) (ψ := 394423/500000) 317 164
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t26 : ((-14388065013/5000000000000 : ℚ) : ℝ) ≤ stT317 26 := by
  have hc : ((-14673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14388065013/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-14673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c27 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((554799/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1228343/5000000) (δ := 1591/100000000) (ψ := 394423/500000) 317 166
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t27 : ((2135036451/20000000000 : ℚ) : ℝ) ≤ stT317 27 := by
  have hc : ((554699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2135036451/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((554699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c28 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((12481/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68919/5000000) (δ := 3977/250000000) (ψ := 394423/500000) 317 168
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t28 : ((47169012209/250000000000 : ℚ) : ℝ) ≤ stT317 28 := by
  have hc : ((49919/50000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47169012209/250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((49919/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c29 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((73167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3743909/10000000) (δ := 8011/500000000) (ψ := 394423/500000) 317 170
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t29 : ((135681984851/10000000000000 : ℚ) : ℝ) ≤ stT317 29 := by
  have hc : ((73067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135681984851/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((73067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c30 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-246157/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3707533/5000000) (δ := 7937/500000000) (ψ := 394423/500000) 317 171
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t30 : ((-112366204261/625000000000 : ℚ) : ℝ) ≤ stT317 30 := by
  have hc : ((-123091/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112366204261/625000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-123091/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c31 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((4381/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 397027/2000000) (δ := 15959/1000000000) (ψ := 394423/500000) 317 173
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t31 : ((62939085279/500000000000 : ℚ) : ℝ) ≤ stT317 31 := by
  have hc : ((35043/50000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62939085279/500000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((35043/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c32 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-136753/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4269947/10000000) (δ := 3209/200000000) (ψ := 394423/500000) 317 175
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t32 : ((-241924217251/10000000000000 : ℚ) : ℝ) ≤ stT317 32 := by
  have hc : ((-136853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241924217251/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-136853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c33 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-23931/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4408583/10000000) (δ := 7969/500000000) (ψ := 394423/500000) 317 176
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t33 : ((-83360588199/2500000000000 : ℚ) : ℝ) ≤ stT317 33 := by
  have hc : ((-47887/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83360588199/2500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-47887/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c34 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((57301/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3348841/10000000) (δ := 3981/250000000) (ψ := 394423/500000) 317 178
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t34 : ((4911374043/125000000000 : ℚ) : ℝ) ≤ stT317 34 := by
  have hc : ((14319/62500 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4911374043/125000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((14319/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c35 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((14/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391579/1000000) (δ := 15987/1000000000) (ψ := 394423/500000) 317 179
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t35 : ((92544363/125000000000 : ℚ) : ℝ) ≤ stT317 35 := by
  have hc : ((219/50000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92544363/125000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((219/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c36 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-478621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5174699/10000000) (δ := 8001/500000000) (ψ := 394423/500000) 317 181
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t36 : ((-797868492907/10000000000000 : ℚ) : ℝ) ≤ stT317 36 := by
  have hc : ((-478721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-797868492907/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-478721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c37 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((118157/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 415523/5000000) (δ := 2001/125000000) (ψ := 394423/500000) 317 182
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t37 : ((388456516821/2500000000000 : ℚ) : ℝ) ≤ stT317 37 := by
  have hc : ((236289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((388456516821/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((236289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c38 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-802967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6257631/10000000) (δ := 3183/200000000) (ψ := 394423/500000) 317 183
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t38 : ((-260549466681/2000000000000 : ℚ) : ℝ) ≤ stT317 38 := by
  have hc : ((-803067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260549466681/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-803067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c39 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-127713/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571589/1250000) (δ := 15873/1000000000) (ψ := 394423/500000) 317 185
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t39 : ((-102292296083/2500000000000 : ℚ) : ℝ) ≤ stT317 39 := by
  have hc : ((-127763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102292296083/2500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-127763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c40 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((996259/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216319/10000000) (δ := 7983/500000000) (ψ := 394423/500000) 317 186
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t40 : ((787532424471/5000000000000 : ℚ) : ℝ) ≤ stT317 40 := by
  have hc : ((996159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((787532424471/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((996159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c41 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((22543/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 911151/2500000) (δ := 4011/250000000) (ψ := 394423/500000) 317 187
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t41 : ((35175002451/2000000000000 : ℚ) : ℝ) ≤ stT317 41 := by
  have hc : ((22523/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35175002451/2000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((22523/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c42 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-946689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1758497/2500000) (δ := 997/62500000) (ψ := 394423/500000) 317 188
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t42 : ((-730463808913/5000000000000 : ℚ) : ℝ) ≤ stT317 42 := by
  have hc : ((-946789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-730463808913/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-946789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c43 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-132299/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5734017/10000000) (δ := 7933/500000000) (ψ := 394423/500000) 317 190
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t43 : ((-100892311267/1000000000000 : ℚ) : ℝ) ≤ stT317 43 := by
  have hc : ((-132319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100892311267/1000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-132319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c44 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((138983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1611401/5000000) (δ := 1603/100000000) (ψ := 394423/500000) 317 191
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t44 : ((52362319437/1250000000000 : ℚ) : ℝ) ≤ stT317 44 := by
  have hc : ((138933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52362319437/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((138933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c45 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((90113/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1121071/10000000) (δ := 15923/1000000000) (ψ := 394423/500000) 317 192
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t45 : ((134317533233/1000000000000 : ℚ) : ℝ) ≤ stT317 45 := by
  have hc : ((90103/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134317533233/1000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((90103/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c46 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((15193/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147311/2500000) (δ := 3979/250000000) (ψ := 394423/500000) 317 193
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t46 : ((358376705397/2500000000000 : ℚ) : ℝ) ≤ stT317 46 := by
  have hc : ((243063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358376705397/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((243063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c47 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((44869/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60157/312500) (δ := 7997/500000000) (ψ := 394423/500000) 317 194
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t47 : ((261756021699/2500000000000 : ℚ) : ℝ) ≤ stT317 47 := by
  have hc : ((179451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261756021699/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((179451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c48 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((7973/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72547/250000) (δ := 7951/500000000) (ψ := 394423/500000) 317 195
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t48 : ((92041137/1600000000 : ℚ) : ℝ) ≤ stT317 48 := by
  have hc : ((7971/20000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92041137/1600000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((7971/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c49 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((1563/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3534633/10000000) (δ := 16009/1000000000) (ψ := 394423/500000) 317 196
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t49 : ((1115713951/50000000000 : ℚ) : ℝ) ≤ stT317 49 := by
  have hc : ((781/5000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1115713951/50000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((781/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c50 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((35833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 959347/2500000) (δ := 15987/1000000000) (ψ := 394423/500000) 317 197
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t50 : ((50534073129/10000000000000 : ℚ) : ℝ) ≤ stT317 50 := by
  have hc : ((35733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50534073129/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((35733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c51 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((4159/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1911493/5000000) (δ := 16023/1000000000) (ψ := 394423/500000) 317 198
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t51 : ((145244043/25000000000 : ℚ) : ℝ) ≤ stT317 51 := by
  have hc : ((4149/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145244043/25000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((4149/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c52 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((168443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3503867/10000000) (δ := 1603/100000000) (ψ := 394423/500000) 317 199
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t52 : ((933798621/40000000000 : ℚ) : ℝ) ≤ stT317 52 := by
  have hc : ((168343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((933798621/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((168343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c53 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((402417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1445801/5000000) (δ := 15937/1000000000) (ψ := 394423/500000) 317 200
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t53 : ((110524928557/2000000000000 : ℚ) : ℝ) ≤ stT317 53 := by
  have hc : ((402317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110524928557/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((402317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c54 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((69753/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 249641/1250000) (δ := 3189/200000000) (ψ := 394423/500000) 317 201
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t54 : ((94908157461/1000000000000 : ℚ) : ℝ) ≤ stT317 54 := by
  have hc : ((69743/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94908157461/1000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((69743/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c55 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((189057/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 415413/5000000) (δ := 15951/1000000000) (ψ := 394423/500000) 317 202
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t55 : ((254897301763/2000000000000 : ℚ) : ℝ) ≤ stT317 55 := by
  have hc : ((189037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254897301763/2000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((189037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c56 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((971577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149369/2500000) (δ := 1993/125000000) (ψ := 394423/500000) 317 203
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t56 : ((649095271981/5000000000000 : ℚ) : ℝ) ≤ stT317 56 := by
  have hc : ((971477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((649095271981/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((971477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c57 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((306319/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139253/5000000) (δ := 7933/500000000) (ψ := 394423/500000) 317 204
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t57 : ((101415772777/1250000000000 : ℚ) : ℝ) ≤ stT317 57 := by
  have hc : ((306269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101415772777/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((306269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c58 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-55183/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1050867/2500000) (δ := 1593/100000000) (ψ := 394423/500000) 317 205
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t58 : ((-14504903829/1000000000000 : ℚ) : ℝ) ≤ stT317 58 := by
  have hc : ((-55233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14504903829/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-55233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c59 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-413809/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6364119/10000000) (δ := 397/25000000) (ψ := 394423/500000) 317 206
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t59 : ((-53879889351/500000000000 : ℚ) : ℝ) ≤ stT317 59 := by
  have hc : ((-413859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53879889351/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-413859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c60 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-58507/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1738877/2500000) (δ := 799/50000000) (ψ := 394423/500000) 317 206
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t60 : ((-60432250547/500000000000 : ℚ) : ℝ) ≤ stT317 60 := by
  have hc : ((-234053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60432250547/500000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-234053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c61 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-8361/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 869403/2000000) (δ := 3997/250000000) (ψ := 394423/500000) 317 207
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t61 : ((-5355783527/250000000000 : ℚ) : ℝ) ≤ stT317 61 := by
  have hc : ((-4183/25000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5355783527/250000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-4183/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c62 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((409767/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 762749/5000000) (δ := 3199/200000000) (ψ := 394423/500000) 317 208
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t62 : ((520340999717/5000000000000 : ℚ) : ℝ) ≤ stT317 62 := by
  have hc : ((409717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520340999717/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((409717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c63 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((16497/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502149/10000000) (δ := 16001/1000000000) (ψ := 394423/500000) 317 209
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t63 : ((4156347419/40000000000 : ℚ) : ℝ) ≤ stT317 63 := by
  have hc : ((3299/4000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4156347419/40000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((3299/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c64 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-315551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295599/625000) (δ := 15909/1000000000) (ψ := 394423/500000) 317 210
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t64 : ((-394564065651/10000000000000 : ℚ) : ℝ) ≤ stT317 64 := by
  have hc : ((-315651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394564065651/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-315651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c65 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-62061/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3778747/5000000) (δ := 7997/500000000) (ψ := 394423/500000) 317 210
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t65 : ((-76984989403/625000000000 : ℚ) : ℝ) ≤ stT317 65 := by
  have hc : ((-248269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76984989403/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-248269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c66 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-4407/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157961/400000) (δ := 3979/250000000) (ψ := 394423/500000) 317 211
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t66 : ((-1097237631/1000000000000 : ℚ) : ℝ) ≤ stT317 66 := by
  have hc : ((-4457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1097237631/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-4457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c67 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((249497/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158597/10000000) (δ := 15979/1000000000) (ψ := 394423/500000) 317 212
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t67 : ((1190540803/9765625000 : ℚ) : ℝ) ≤ stT317 67 := by
  have hc : ((15592/15625 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1190540803/9765625000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((15592/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c68 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((47419/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3808399/10000000) (δ := 15931/1000000000) (ψ := 394423/500000) 317 213
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t68 : ((28691355141/5000000000000 : ℚ) : ℝ) ≤ stT317 68 := by
  have hc : ((47319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28691355141/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((47319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c69 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-999311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155223/200000) (δ := 15931/1000000000) (ψ := 394423/500000) 317 213
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t69 : ((-1203149927049/10000000000000 : ℚ) : ℝ) ≤ stT317 69 := by
  have hc : ((-999411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1203149927049/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-999411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c70 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((187193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3456231/10000000) (δ := 3193/200000000) (ψ := 394423/500000) 317 214
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t70 : ((55904698051/2500000000000 : ℚ) : ℝ) ≤ stT317 70 := by
  have hc : ((187093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55904698051/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((187093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c71 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((919427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252609/2500000) (δ := 3209/200000000) (ψ := 394423/500000) 317 215
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t71 : ((1091039816387/10000000000000 : ℚ) : ℝ) ≤ stT317 71 := by
  have hc : ((919327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1091039816387/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((919327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c72 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-12621/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5634257/10000000) (δ := 3963/250000000) (ψ := 394423/500000) 317 216
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t72 : ((-929772311/12500000000 : ℚ) : ℝ) ≤ stT317 72 := by
  have hc : ((-12623/20000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-929772311/12500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-12623/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c73 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-520961/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5296933/10000000) (δ := 15951/1000000000) (ψ := 394423/500000) 317 216
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t73 : ((-152464011783/2500000000000 : ℚ) : ℝ) ≤ stT317 73 := by
  have hc : ((-521061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152464011783/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-521061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c74 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((197797/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23213/625000) (δ := 15859/1000000000) (ψ := 394423/500000) 317 217
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t74 : ((57477753963/500000000000 : ℚ) : ℝ) ≤ stT317 74 := by
  have hc : ((197777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57477753963/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((197777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c75 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-303823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4698749/10000000) (δ := 4009/250000000) (ψ := 394423/500000) 317 218
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t75 : ((-350940192023/10000000000000 : ℚ) : ℝ) ≤ stT317 75 := by
  have hc : ((-303923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350940192023/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-303923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c76 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-680491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724759/1250000) (δ := 4009/250000000) (ψ := 394423/500000) 317 218
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t76 : ((-780691643689/10000000000000 : ℚ) : ℝ) ≤ stT317 76 := by
  have hc : ((-680591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-780691643689/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-680591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c77 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((491931/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 112437/2500000) (δ := 16029/1000000000) (ψ := 394423/500000) 317 219
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t77 : ((112110009401/1000000000000 : ℚ) : ℝ) ≤ stT317 77 := by
  have hc : ((491881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112110009401/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((491881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c78 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-427849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503227/1000000) (δ := 15981/1000000000) (ψ := 394423/500000) 317 220
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t78 : ((-242278618911/5000000000000 : ℚ) : ℝ) ≤ stT317 78 := by
  have hc : ((-427949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242278618911/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-427949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c79 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-219533/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5063387/10000000) (δ := 7961/500000000) (ψ := 394423/500000) 317 220
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t79 : ((-7720318697/156250000000 : ℚ) : ℝ) ≤ stT317 79 := by
  have hc : ((-219583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7720318697/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-219583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c80 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((963677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -675877/10000000) (δ := 993/62500000) (ψ := 394423/500000) 317 221
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t80 : ((1077310884041/10000000000000 : ℚ) : ℝ) ≤ stT317 80 := by
  have hc : ((963577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1077310884041/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((963577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c81 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-216207/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6539009/10000000) (δ := 3179/200000000) (ψ := 394423/500000) 317 222
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t81 : ((-3754030781/39062500000 : ℚ) : ℝ) ≤ stT317 81 := by
  have hc : ((-27029/31250 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3754030781/39062500000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-27029/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c82 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((292441/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 637009/2000000) (δ := 3977/250000000) (ψ := 394423/500000) 317 222
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t82 : ((64567310283/2000000000000 : ℚ) : ℝ) ≤ stT317 82 := by
  have hc : ((292341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64567310283/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((292341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c83 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((393203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2916709/10000000) (δ := 1/62500) (ψ := 394423/500000) 317 223
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t83 : ((215743181563/5000000000000 : ℚ) : ℝ) ≤ stT317 83 := by
  have hc : ((393103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215743181563/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((393103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c84 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-435923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 657439/1000000) (δ := 159/5000000) (ψ := 394423/500000) 317 223
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t84 : ((-47568578057/500000000000 : ℚ) : ℝ) ≤ stT317 84 := by
  have hc : ((-435973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47568578057/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-435973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c85 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((995193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245229/10000000) (δ := 1601/100000000) (ψ := 394423/500000) 317 224
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t85 : ((269832403159/2500000000000 : ℚ) : ℝ) ≤ stT317 85 := by
  have hc : ((995093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269832403159/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((995093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c86 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-787453/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1238731/2000000) (δ := 7993/500000000) (ψ := 394423/500000) 317 225
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t86 : ((-106155056423/1250000000000 : ℚ) : ℝ) ≤ stT317 86 := by
  have hc : ((-787553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106155056423/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-787553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c87 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((2993/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2968359/10000000) (δ := 16017/1000000000) (ψ := 394423/500000) 317 225
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t87 : ((1002491727/25000000000 : ℚ) : ℝ) ≤ stT317 87 := by
  have hc : ((14961/40000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1002491727/25000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((14961/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c88 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((3053/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92059/250000) (δ := 15879/1000000000) (ψ := 394423/500000) 317 226
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t88 : ((26009407197/2500000000000 : ℚ) : ℝ) ≤ stT317 88 := by
  have hc : ((24399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26009407197/2500000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((24399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c89 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-32037/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2636247/5000000) (δ := 3981/250000000) (ψ := 394423/500000) 317 226
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t89 : ((-67931561827/1250000000000 : ℚ) : ℝ) ≤ stT317 89 := by
  have hc : ((-128173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67931561827/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-128173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c90 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((806699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1580629/10000000) (δ := 15931/1000000000) (ψ := 394423/500000) 317 227
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t90 : ((212557388277/2500000000000 : ℚ) : ℝ) ≤ stT317 90 := by
  have hc : ((806599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212557388277/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((806599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c91 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-240873/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7176377/10000000) (δ := 31731/1000000000) (ψ := 394423/500000) 317 227
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t91 : ((-25252975993/250000000000 : ℚ) : ℝ) ≤ stT317 91 := by
  have hc : ((-120449/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25252975993/250000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-120449/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c92 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((199731/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64843/5000000) (δ := 7969/500000000) (ψ := 394423/500000) 317 228
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t92 : ((52053274173/500000000000 : ℚ) : ℝ) ≤ stT317 92 := by
  have hc : ((199711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52053274173/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((199711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c93 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-943639/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7010639/10000000) (δ := 7973/500000000) (ψ := 394423/500000) 317 229
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t93 : ((-122326505441/1250000000000 : ℚ) : ℝ) ≤ stT317 93 := by
  have hc : ((-943739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122326505441/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-943739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c94 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((416537/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 732693/5000000) (δ := 15857/1000000000) (ψ := 394423/500000) 317 229
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t94 : ((429573438027/5000000000000 : ℚ) : ℝ) ≤ stT317 94 := by
  have hc : ((416487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429573438027/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((416487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c95 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-697361/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5856263/10000000) (δ := 15853/1000000000) (ψ := 394423/500000) 317 230
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t95 : ((-715580339319/10000000000000 : ℚ) : ℝ) ≤ stT317 95 := by
  have hc : ((-697461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-715580339319/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-697461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c96 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((559597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1221121/5000000) (δ := 319/20000000) (ψ := 394423/500000) 317 230
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t96 : ((28551691407/500000000000 : ℚ) : ℝ) ≤ stT317 96 := by
  have hc : ((559497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28551691407/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((559497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c97 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-217701/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2526601/5000000) (δ := 793/50000000) (ψ := 394423/500000) 317 231
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t97 : ((-221092824597/5000000000000 : ℚ) : ℝ) ≤ stT317 97 := by
  have hc : ((-217751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221092824597/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-217751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c98 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((33421/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1537537/5000000) (δ := 15943/1000000000) (ψ := 394423/500000) 317 231
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t98 : ((4218773559/125000000000 : ℚ) : ℝ) ≤ stT317 98 := by
  have hc : ((33411/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4218773559/125000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((33411/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c99 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-260991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -573389/1250000) (δ := 15867/1000000000) (ψ := 394423/500000) 317 232
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t99 : ((-131203188229/5000000000000 : ℚ) : ℝ) ≤ stT317 99 := by
  have hc : ((-261091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131203188229/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-261091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c100 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((217933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3377751/10000000) (δ := 15967/1000000000) (ψ := 394423/500000) 317 232
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t100 : ((217832782167/10000000000000 : ℚ) : ℝ) ≤ stT317 100 := by
  have hc : ((217833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217832782167/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((217833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c101 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-205537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4444521/10000000) (δ := 16029/1000000000) (ψ := 394423/500000) 317 233
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t101 : ((-102308314603/5000000000000 : ℚ) : ℝ) ≤ stT317 101 := by
  have hc : ((-205637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102308314603/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-205637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c102 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((223521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3363427/10000000) (δ := 15929/1000000000) (ψ := 394423/500000) 317 233
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t102 : ((221219632887/10000000000000 : ℚ) : ℝ) ≤ stT317 102 := by
  have hc : ((223421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221219632887/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((223421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c103 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-135453/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4612827/10000000) (δ := 15921/1000000000) (ψ := 394423/500000) 317 234
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t103 : ((-13351517099/500000000000 : ℚ) : ℝ) ≤ stT317 103 := by
  have hc : ((-135503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13351517099/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-135503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c104 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((345813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3044229/10000000) (δ := 7941/500000000) (ψ := 394423/500000) 317 234
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t104 : ((16949962677/500000000000 : ℚ) : ℝ) ≤ stT317 104 := by
  have hc : ((345713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16949962677/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((345713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c105 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-444993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2539953/5000000) (δ := 8007/500000000) (ψ := 394423/500000) 317 235
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t105 : ((-434366703793/10000000000000 : ℚ) : ℝ) ≤ stT317 105 := by
  have hc : ((-445093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434366703793/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-445093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c106 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((563/1000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 607991/2500000) (δ := 7957/500000000) (ψ := 394423/500000) 317 235
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t106 : ((1093472653/20000000000 : ℚ) : ℝ) ≤ stT317 106 := by
  have hc : ((5629/10000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1093472653/20000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((5629/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c107 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-8639/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5834583/10000000) (δ := 16007/1000000000) (ψ := 394423/500000) 317 236
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t107 : ((-33411397457/500000000000 : ℚ) : ℝ) ≤ stT317 107 := by
  have hc : ((-34561/50000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33411397457/500000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-34561/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c108 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((408379/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1537569/10000000) (δ := 16007/1000000000) (ψ := 394423/500000) 317 236
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t108 : ((1571658321/20000000000 : ℚ) : ℝ) ≤ stT317 108 := by
  have hc : ((408329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1571658321/20000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((408329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c109 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-922959/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3433119/5000000) (δ := 16003/1000000000) (ψ := 394423/500000) 317 237
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t109 : ((-884130832793/10000000000000 : ℚ) : ℝ) ≤ stT317 109 := by
  have hc : ((-923059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-884130832793/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-923059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c110 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((988993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92817/2500000) (δ := 15903/1000000000) (ψ := 394423/500000) 317 237
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t110 : ((471435948783/5000000000000 : ℚ) : ℝ) ≤ stT317 110 := by
  have hc : ((988893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471435948783/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((988893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c111 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-992289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3771657/5000000) (δ := 16003/1000000000) (ψ := 394423/500000) 317 237
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t111 : ((-470966979231/5000000000000 : ℚ) : ℝ) ≤ stT317 111 := by
  have hc : ((-992389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470966979231/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-992389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c112 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((455969/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -528517/5000000) (δ := 1591/100000000) (ψ := 394423/500000) 317 238
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t112 : ((430802878209/5000000000000 : ℚ) : ℝ) ≤ stT317 112 := by
  have hc : ((455919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430802878209/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((455919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c113 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-734007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2993749/5000000) (δ := 15993/1000000000) (ψ := 394423/500000) 317 238
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t113 : ((-690589871147/10000000000000 : ℚ) : ℝ) ≤ stT317 113 := by
  have hc : ((-734107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-690589871147/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-734107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c114 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((228923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171129/625000) (δ := 16017/1000000000) (ψ := 394423/500000) 317 239
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t114 : ((42871803741/1000000000000 : ℚ) : ℝ) ≤ stT317 114 := by
  have hc : ((228873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42871803741/1000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((228873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c115 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-102381/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4183393/10000000) (δ := 15917/1000000000) (ψ := 394423/500000) 317 239
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t115 : ((-19112808981/2000000000000 : ℚ) : ℝ) ≤ stT317 115 := by
  have hc : ((-102481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19112808981/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-102481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c116 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-290209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932621/2000000) (δ := 641/40000000) (ψ := 394423/500000) 317 240
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t116 : ((-269545229393/10000000000000 : ℚ) : ℝ) ≤ stT317 116 := by
  have hc : ((-290309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269545229393/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-290309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c117 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((327799/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534889/2500000) (δ := 7939/500000000) (ψ := 394423/500000) 317 240
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t117 : ((606007901/10000000000 : ℚ) : ℝ) ≤ stT317 117 := by
  have hc : ((327749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606007901/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((327749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c118 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-916273/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6823677/10000000) (δ := 501/31250000) (ψ := 394423/500000) 317 241
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t118 : ((-33743602979/400000000000 : ℚ) : ℝ) ≤ stT317 118 := by
  have hc : ((-916373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33743602979/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-916373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c119 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((499261/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16991/1250000) (δ := 501/31250000) (ψ := 394423/500000) 317 241
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t119 : ((228812862639/2500000000000 : ℚ) : ℝ) ≤ stT317 119 := by
  have hc : ((499211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228812862639/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((499211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c120 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-214013/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6495949/10000000) (δ := 15971/1000000000) (ψ := 394423/500000) 317 241
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t120 : ((-97694541549/1250000000000 : ℚ) : ℝ) ≤ stT317 120 := by
  have hc : ((-107019/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97694541549/1250000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-107019/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c121 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((494023/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -527043/2000000) (δ := 1983/125000000) (ψ := 394423/500000) 317 242
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t121 : ((44902046007/1000000000000 : ℚ) : ℝ) ≤ stT317 121 := by
  have hc : ((493923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44902046007/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((493923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c122 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((15813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121483/312500) (δ := 3991/250000000) (ψ := 394423/500000) 317 242
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t122 : ((14225874541/10000000000000 : ℚ) : ℝ) ≤ stT317 122 := by
  have hc : ((15713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14225874541/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((15713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c123 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-539329/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1337773/2500000) (δ := 15957/1000000000) (ψ := 394423/500000) 317 243
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t123 : ((-48638694643/1000000000000 : ℚ) : ℝ) ≤ stT317 123 := by
  have hc : ((-539429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48638694643/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-539429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c124 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((910471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1065939/10000000) (δ := 15957/1000000000) (ψ := 394423/500000) 317 243
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t124 : ((408768413823/5000000000000 : ℚ) : ℝ) ≤ stT317 124 := by
  have hc : ((910371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408768413823/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((910371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c125 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-123219/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3715729/5000000) (δ := 7973/500000000) (ψ := 394423/500000) 317 243
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t125 : ((-55110852041/625000000000 : ℚ) : ℝ) ≤ stT317 125 := by
  have hc : ((-246463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55110852041/625000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-246463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c126 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((176903/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1961707/10000000) (δ := 15853/1000000000) (ψ := 394423/500000) 317 244
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t126 : ((7878765193/125000000000 : ℚ) : ℝ) ≤ stT317 126 := by
  have hc : ((88439/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7878765193/125000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((88439/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c127 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-149871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 860617/2000000) (δ := 15953/1000000000) (ψ := 394423/500000) 317 244
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t127 : ((-133077816647/10000000000000 : ℚ) : ℝ) ≤ stT317 127 := by
  have hc : ((-149971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133077816647/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-149971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c128 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-241843/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5189143/10000000) (δ := 16043/1000000000) (ψ := 394423/500000) 317 245
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t128 : ((-53451338103/1250000000000 : ℚ) : ℝ) ≤ stT317 128 := by
  have hc : ((-241893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53451338103/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-241893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c129 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((462207/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 978251/10000000) (δ := 793/50000000) (ψ := 394423/500000) 317 245
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t129 : ((8138122613/100000000000 : ℚ) : ℝ) ≤ stT317 129 := by
  have hc : ((462157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8138122613/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((462157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c130 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-954619/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443621/625000) (δ := 793/50000000) (ψ := 394423/500000) 317 245
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t130 : ((-837344891421/10000000000000 : ℚ) : ℝ) ≤ stT317 130 := by
  have hc : ((-954719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-837344891421/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-954719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c131 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((527729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2537179/10000000) (δ := 3967/250000000) (ψ := 394423/500000) 317 246
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t131 : ((57623945977/1250000000000 : ℚ) : ℝ) ≤ stT317 131 := by
  have hc : ((527629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57623945977/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((527629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c132 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((87059/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1744733/5000000) (δ := 3207/200000000) (ψ := 394423/500000) 317 246
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t132 : ((18932897373/1250000000000 : ℚ) : ℝ) ≤ stT317 132 := by
  have hc : ((87009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18932897373/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((87009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c133 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-798103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6237341/10000000) (δ := 1991/125000000) (ψ := 394423/500000) 317 247
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t133 : ((-69212980333/1000000000000 : ℚ) : ℝ) ≤ stT317 133 := by
  have hc : ((-798203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69212980333/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-798203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c134 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((992761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301001/10000000) (δ := 7957/250000000) (ψ := 394423/500000) 317 247
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t134 : ((214382018187/2500000000000 : ℚ) : ℝ) ≤ stT317 134 := by
  have hc : ((992661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214382018187/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((992661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c135 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-154399/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5591197/10000000) (δ := 1991/125000000) (ψ := 394423/500000) 317 247
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t135 : ((-16613377889/312500000000 : ℚ) : ℝ) ≤ stT317 135 := by
  have hc : ((-19303/31250 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16613377889/312500000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-19303/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c136 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-33999/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4268037/10000000) (δ := 15921/1000000000) (ψ := 394423/500000) 317 248
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t136 : ((-3646917729/312500000000 : ℚ) : ℝ) ≤ stT317 136 := by
  have hc : ((-4253/31250 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3646917729/312500000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-4253/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c137 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((408341/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1537897/10000000) (δ := 16021/1000000000) (ψ := 394423/500000) 317 248
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t137 : ((348826273887/5000000000000 : ℚ) : ℝ) ≤ stT317 137 := by
  have hc : ((408291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348826273887/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((408291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c138 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-975681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912689/1250000) (δ := 15921/1000000000) (ψ := 394423/500000) 317 248
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t138 : ((-830640406717/10000000000000 : ℚ) : ℝ) ≤ stT317 138 := by
  have hc : ((-975781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-830640406717/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-975781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c139 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((119209/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2684363/10000000) (δ := 15989/1000000000) (ψ := 394423/500000) 317 249
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t139 : ((1579538103/39062500000 : ℚ) : ℝ) ≤ stT317 139 := by
  have hc : ((7449/15625 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1579538103/39062500000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((7449/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c140 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((181799/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2996673/10000000) (δ := 15889/1000000000) (ψ := 394423/500000) 317 249
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t140 : ((76802947173/2500000000000 : ℚ) : ℝ) ≤ stT317 140 := by
  have hc : ((181749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76802947173/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((181749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c141 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-237831/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7070751/10000000) (δ := 15907/1000000000) (ψ := 394423/500000) 317 250
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t141 : ((-782464477/9765625000 : ℚ) : ℝ) ≤ stT317 141 := by
  have hc : ((-14866/15625 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-782464477/9765625000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-14866/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c142 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((832053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293999/2000000) (δ := 15907/1000000000) (ψ := 394423/500000) 317 250
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t142 : ((698159150493/10000000000000 : ℚ) : ℝ) ≤ stT317 142 := by
  have hc : ((831953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((698159150493/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((831953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c143 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-65737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4091453/10000000) (δ := 15907/1000000000) (ψ := 394423/500000) 317 250
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t143 : ((-55055730391/10000000000000 : ℚ) : ℝ) ≤ stT317 143 := by
  have hc : ((-65837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55055730391/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-65837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c144 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-762237/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1218779/2000000) (δ := 15999/1000000000) (ψ := 394423/500000) 317 251
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t144 : ((-317640670779/5000000000000 : ℚ) : ℝ) ≤ stT317 144 := by
  have hc : ((-762337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-317640670779/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-762337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c145 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((485219/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -304699/5000000) (δ := 4001/250000000) (ψ := 394423/500000) 317 251
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t145 : ((201455268363/2500000000000 : ℚ) : ℝ) ≤ stT317 145 := by
  have hc : ((485169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201455268363/2500000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((485169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c146 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-356159/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38699/80000) (δ := 497/31250000) (ψ := 394423/500000) 317 251
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t146 : ((-147421042977/5000000000000 : ℚ) : ℝ) ≤ stT317 146 := by
  have hc : ((-356259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147421042977/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-356259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c147 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-287919/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5461063/10000000) (δ := 1999/125000000) (ψ := 394423/500000) 317 252
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t147 : ((-237513087603/5000000000000 : ℚ) : ℝ) ≤ stT317 147 := by
  have hc : ((-287969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237513087603/5000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-287969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c148 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((499689/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1763/200000) (δ := 16011/1000000000) (ψ := 394423/500000) 317 252
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t148 : ((205350130083/2500000000000 : ℚ) : ℝ) ≤ stT317 148 := by
  have hc : ((499639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205350130083/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((499639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c149 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-504371/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328039/625000) (δ := 15911/1000000000) (ψ := 394423/500000) 317 252
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t149 : ((-12914962071/312500000000 : ℚ) : ℝ) ≤ stT317 149 := by
  have hc : ((-504471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12914962071/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-504471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c150 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-472881/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2579193/5000000) (δ := 7959/500000000) (ψ := 394423/500000) 317 253
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t150 : ((-386187567557/10000000000000 : ℚ) : ℝ) ≤ stT317 150 := by
  have hc : ((-472981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386187567557/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-472981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c151 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((249769/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107459/10000000) (δ := 3197/200000000) (ψ := 394423/500000) 317 253
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t151 : ((3175604223/39062500000 : ℚ) : ℝ) ≤ stT317 151 := by
  have hc : ((15609/15625 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3175604223/39062500000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((15609/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c152 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-267543/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2669257/5000000) (δ := 3177/200000000) (ψ := 394423/500000) 317 253
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t152 : ((-54261705761/1250000000000 : ℚ) : ℝ) ≤ stT317 152 := by
  have hc : ((-267593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54261705761/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-267593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c153 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-238961/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -517271/1000000) (δ := 7989/500000000) (ψ := 394423/500000) 317 254
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t153 : ((-193229159983/5000000000000 : ℚ) : ℝ) ≤ stT317 153 := by
  have hc : ((-239011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193229159983/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-239011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c154 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((124999/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -981/1000000) (δ := 7939/500000000) (ψ := 394423/500000) 317 254
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t154 : ((100716871403/1250000000000 : ℚ) : ℝ) ≤ stT317 154 := by
  have hc : ((249973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100716871403/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((249973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c155 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-459171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2559823/5000000) (δ := 7989/500000000) (ψ := 394423/500000) 317 254
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t155 : ((-18444782631/500000000000 : ℚ) : ℝ) ≤ stT317 155 := by
  have hc : ((-459271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18444782631/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-459271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c156 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-117171/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5491829/10000000) (δ := 15971/1000000000) (ψ := 394423/500000) 317 255
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t156 : ((-93827919431/2000000000000 : ℚ) : ℝ) ≤ stT317 156 := by
  have hc : ((-117191/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93827919431/2000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-117191/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c157 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((985387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53489/1250000) (δ := 3983/250000000) (ψ := 394423/500000) 317 255
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t157 : ((393171880341/5000000000000 : ℚ) : ℝ) ≤ stT317 157 := by
  have hc : ((985287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((393171880341/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((985287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c158 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-3343/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4603829/10000000) (δ := 3983/250000000) (ψ := 394423/500000) 317 255
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t158 : ((-5321089683/250000000000 : ℚ) : ℝ) ≤ stT317 158 := by
  have hc : ((-13377/50000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5321089683/250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-13377/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c159 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-764871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6104093/10000000) (δ := 16039/1000000000) (ψ := 394423/500000) 317 256
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t159 : ((-151665445373/2500000000000 : ℚ) : ℝ) ≤ stT317 159 := by
  have hc : ((-764971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151665445373/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-764971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c160 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((14041/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227087/2000000) (δ := 16039/1000000000) (ψ := 394423/500000) 317 256
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t160 : ((177586305039/2500000000000 : ℚ) : ℝ) ≤ stT317 160 := by
  have hc : ((224631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177586305039/2500000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((224631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c161 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((49881/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 950559/2500000) (δ := 15939/1000000000) (ψ := 394423/500000) 317 256
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t161 : ((3923290391/1000000000000 : ℚ) : ℝ) ≤ stT317 161 := by
  have hc : ((49781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3923290391/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((49781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c162 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-94203/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6998567/10000000) (δ := 16047/1000000000) (ψ := 394423/500000) 317 257
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t162 : ((-2960831951/40000000000 : ℚ) : ℝ) ≤ stT317 162 := by
  have hc : ((-94213/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2960831951/40000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-94213/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c163 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((165251/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1060801/5000000) (δ := 3989/250000000) (ψ := 394423/500000) 317 257
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t163 : ((3235372919/62500000000 : ℚ) : ℝ) ≤ stT317 163 := by
  have hc : ((82613/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3235372919/62500000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((82613/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c164 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((462313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2725487/10000000) (δ := 15947/1000000000) (ψ := 394423/500000) 317 257
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t164 : ((90231835221/2500000000000 : ℚ) : ℝ) ≤ stT317 164 := by
  have hc : ((462213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90231835221/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((462213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c165 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-496139/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3771547/5000000) (δ := 3989/250000000) (ψ := 394423/500000) 317 257
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t165 : ((-386282640311/5000000000000 : ℚ) : ℝ) ≤ stT317 165 := by
  have hc : ((-496189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386282640311/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-496189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c166 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((218481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1688173/5000000) (δ := 7977/500000000) (ψ := 394423/500000) 317 258
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t166 : ((3389928263/200000000000 : ℚ) : ℝ) ≤ stT317 166 := by
  have hc : ((218381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3389928263/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((218381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c167 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((170149/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21617/156250) (δ := 7927/500000000) (ψ := 394423/500000) 317 258
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t167 : ((131649733167/2000000000000 : ℚ) : ℝ) ≤ stT317 167 := by
  have hc : ((170129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131649733167/2000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((170129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c168 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-767621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 764349/1250000) (δ := 15949/1000000000) (ψ := 394423/500000) 317 258
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t168 : ((-592309802757/10000000000000 : ℚ) : ℝ) ≤ stT317 168 := by
  have hc : ((-767721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592309802757/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-767721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c169 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-375689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2444921/5000000) (δ := 15861/1000000000) (ψ := 394423/500000) 317 259
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t169 : ((-289068548259/10000000000000 : ℚ) : ℝ) ≤ stT317 169 := by
  have hc : ((-375789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289068548259/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-375789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c170 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((996327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21433/1000000) (δ := 7971/500000000) (ψ := 394423/500000) 317 259
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t170 : ((191017561207/2500000000000 : ℚ) : ℝ) ≤ stT317 170 := by
  have hc : ((996227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191017561207/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((996227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c171 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-201323/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2216881/5000000) (δ := 15861/1000000000) (ψ := 394423/500000) 317 259
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t171 : ((-1925402457/125000000000 : ℚ) : ℝ) ≤ stT317 171 := by
  have hc : ((-201423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1925402457/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-201423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c172 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-886853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6653213/10000000) (δ := 3967/250000000) (ψ := 394423/500000) 317 260
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t172 : ((-676295453829/10000000000000 : ℚ) : ℝ) ≤ stT317 172 := by
  have hc : ((-886953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-676295453829/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-886953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c173 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((679581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2059011/10000000) (δ := 499/31250000) (ψ := 394423/500000) 317 260
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t173 : ((103319842417/2000000000000 : ℚ) : ℝ) ≤ stT317 173 := by
  have hc : ((679481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103319842417/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((679481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c174 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((134341/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2508721/10000000) (δ := 3967/250000000) (ψ := 394423/500000) 317 260
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t174 : ((12728086371/312500000000 : ℚ) : ℝ) ≤ stT317 174 := by
  have hc : ((33579/62500 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12728086371/312500000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((33579/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c175 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-948771/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7050301/10000000) (δ := 499/31250000) (ψ := 394423/500000) 317 260
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t175 : ((-717279106159/10000000000000 : ℚ) : ℝ) ≤ stT317 175 := by
  have hc : ((-948871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-717279106159/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-948871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c176 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-85897/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2070999/5000000) (δ := 4007/250000000) (ψ := 394423/500000) 317 261
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t176 : ((-64822732663/10000000000000 : ℚ) : ℝ) ≤ stT317 176 := by
  have hc : ((-85997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64822732663/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-85997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c177 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((990319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348149/10000000) (δ := 127/8000000) (ψ := 394423/500000) 317 261
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t177 : ((372147075237/5000000000000 : ℚ) : ℝ) ≤ stT317 177 := by
  have hc : ((990219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372147075237/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((990219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c178 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-347007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 962587/2000000) (δ := 4007/250000000) (ψ := 394423/500000) 317 261
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t178 : ((-65041950981/2500000000000 : ℚ) : ℝ) ≤ stT317 178 := by
  have hc : ((-347107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65041950981/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-347107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c179 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-169503/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1291041/2000000) (δ := 15883/1000000000) (ψ := 394423/500000) 317 262
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t179 : ((-31676898257/500000000000 : ℚ) : ℝ) ≤ stT317 179 := by
  have hc : ((-169523/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31676898257/500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-169523/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c180 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((342543/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -510047/2500000) (δ := 801/50000000) (ψ := 394423/500000) 317 262
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t180 : ((51055774003/1000000000000 : ℚ) : ℝ) ≤ stT317 180 := by
  have hc : ((342493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51055774003/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((342493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c181 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((147413/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2350421/10000000) (δ := 15883/1000000000) (ψ := 394423/500000) 317 262
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t181 : ((13694077009/312500000000 : ℚ) : ℝ) ≤ stT317 181 := by
  have hc : ((36847/62500 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13694077009/312500000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((36847/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c182 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-898313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6716779/10000000) (δ := 15883/1000000000) (ψ := 394423/500000) 317 262
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t182 : ((-532758909/8000000000 : ℚ) : ℝ) ≤ stT317 182 := by
  have hc : ((-898413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-532758909/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-898413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c183 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-284683/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4648681/10000000) (δ := 16013/1000000000) (ψ := 394423/500000) 317 263
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t183 : ((-105258929413/5000000000000 : ℚ) : ℝ) ≤ stT317 183 := by
  have hc : ((-284783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105258929413/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-284783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c184 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((991307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329873/10000000) (δ := 16013/1000000000) (ψ := 394423/500000) 317 263
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t184 : ((730726721263/10000000000000 : ℚ) : ℝ) ≤ stT317 184 := by
  have hc : ((991207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((730726721263/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((991207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c185 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-7713/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3965557/10000000) (δ := 1599/100000000) (ψ := 394423/500000) 317 263
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t185 : ((-1141494809/1000000000000 : ℚ) : ℝ) ≤ stT317 185 := by
  have hc : ((-7763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1141494809/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-7763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c186 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-12353/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3735099/5000000) (δ := 8003/500000000) (ψ := 394423/500000) 317 264
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t186 : ((-9058580853/125000000000 : ℚ) : ℝ) ≤ stT317 186 := by
  have hc : ((-49417/50000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9058580853/125000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-49417/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c187 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((27873/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3220813/10000000) (δ := 8003/500000000) (ψ := 394423/500000) 317 264
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t187 : ((2546928967/125000000000 : ℚ) : ℝ) ≤ stT317 187 := by
  have hc : ((27863/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2546928967/125000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((27863/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c188 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((920151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251457/2500000) (δ := 15997/1000000000) (ψ := 394423/500000) 317 264
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t188 : ((167753818881/2500000000000 : ℚ) : ℝ) ≤ stT317 188 := by
  have hc : ((920051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167753818881/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((920051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c189 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-122753/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5210119/10000000) (δ := 8003/500000000) (ψ := 394423/500000) 317 264
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t189 : ((-44653928877/1250000000000 : ℚ) : ℝ) ≤ stT317 189 := by
  have hc : ((-61389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44653928877/1250000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-61389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c190 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-816621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6315821/10000000) (δ := 4001/250000000) (ψ := 394423/500000) 317 265
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t190 : ((-592512300917/10000000000000 : ℚ) : ℝ) ≤ stT317 190 := by
  have hc : ((-816721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592512300917/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-816721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c191 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((162679/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269459/1250000) (δ := 15899/1000000000) (ψ := 394423/500000) 317 265
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t191 : ((29423051349/625000000000 : ℚ) : ℝ) ≤ stT317 191 := by
  have hc : ((81327/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29423051349/625000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((81327/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c192 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((701659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 495671/2500000) (δ := 497/31250000) (ψ := 394423/500000) 317 265
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t192 : ((506306010033/10000000000000 : ℚ) : ℝ) ≤ stT317 192 := by
  have hc : ((701559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506306010033/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((701559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c193 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-381851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6099563/10000000) (δ := 497/31250000) (ψ := 394423/500000) 317 265
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t193 : ((-34362306277/625000000000 : ℚ) : ℝ) ≤ stT317 193 := by
  have hc : ((-381901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34362306277/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-381901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c194 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-29631/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137819/250000) (δ := 16011/1000000000) (ψ := 394423/500000) 317 266
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t194 : ((-5319358231/125000000000 : ℚ) : ℝ) ≤ stT317 194 := by
  have hc : ((-7409/12500 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5319358231/125000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-7409/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c195 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((2622/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1438201/10000000) (δ := 3973/250000000) (ψ := 394423/500000) 317 266
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t195 : ((15019416979/250000000000 : ℚ) : ℝ) ≤ stT317 195 := by
  have hc : ((41947/50000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15019416979/250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((41947/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c196 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((250429/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653879/2500000) (δ := 15911/1000000000) (ψ := 394423/500000) 317 266
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t196 : ((35768392803/1000000000000 : ℚ) : ℝ) ≤ stT317 196 := by
  have hc : ((250379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35768392803/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((250379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c197 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-221501/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1662157/2500000) (δ := 16011/1000000000) (ψ := 394423/500000) 317 266
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t197 : ((-78915425373/1250000000000 : ℚ) : ℝ) ≤ stT317 197 := by
  have hc : ((-110763/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78915425373/1250000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-110763/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c198 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-54131/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -504667/1000000) (δ := 8009/500000000) (ψ := 394423/500000) 317 267
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t198 : ((-7695632229/250000000000 : ℚ) : ℝ) ≤ stT317 198 := by
  have hc : ((-108287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7695632229/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-108287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c199 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((2281/2500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -527107/5000000) (δ := 3177/200000000) (ψ := 394423/500000) 317 267
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t199 : ((6467121363/100000000000 : ℚ) : ℝ) ≤ stT317 199 := by
  have hc : ((9123/10000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6467121363/100000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((9123/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c200 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((196329/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182387/625000) (δ := 3197/200000000) (ψ := 394423/500000) 317 267
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t200 : ((69395029287/2500000000000 : ℚ) : ℝ) ≤ stT317 200 := by
  have hc : ((196279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69395029287/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((196279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c201 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-92367/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374173/2000000) (δ := 3197/200000000) (ψ := 394423/500000) 317 267
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t201 : ((-32578873721/500000000000 : ℚ) : ℝ) ≤ stT317 201 := by
  have hc : ((-92377/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32578873721/500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-92377/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c202 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-38099/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2452079/5000000) (δ := 7963/500000000) (ψ := 394423/500000) 317 268
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t202 : ((-13406708091/500000000000 : ℚ) : ℝ) ≤ stT317 202 := by
  have hc : ((-38109/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13406708091/500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-38109/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c203 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((461263/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198111/2000000) (δ := 8013/500000000) (ψ := 394423/500000) 317 268
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t203 : ((161853939303/2500000000000 : ℚ) : ℝ) ≤ stT317 203 := by
  have hc : ((461213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161853939303/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((461213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c204 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((397949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290379/1000000) (δ := 8013/500000000) (ψ := 394423/500000) 317 268
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t204 : ((13927499943/500000000000 : ℚ) : ℝ) ≤ stT317 204 := by
  have hc : ((397849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13927499943/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((397849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c205 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-227247/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1355823/2000000) (δ := 8013/500000000) (ψ := 394423/500000) 317 268
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t205 : ((-19841726279/312500000000 : ℚ) : ℝ) ≤ stT317 205 := by
  have hc : ((-28409/31250 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19841726279/312500000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-28409/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c206 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-442297/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1014477/2000000) (δ := 15933/1000000000) (ψ := 394423/500000) 317 269
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t206 : ((-154116515699/5000000000000 : ℚ) : ℝ) ≤ stT317 206 := by
  have hc : ((-442397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154116515699/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-442397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c207 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((440257/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9877/80000) (δ := 1597/100000000) (ψ := 394423/500000) 317 269
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t207 : ((38245624367/625000000000 : ℚ) : ℝ) ≤ stT317 207 := by
  have hc : ((440207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38245624367/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((440207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c208 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((511499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2584671/10000000) (δ := 16033/1000000000) (ψ := 394423/500000) 317 269
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t208 : ((2836730253/80000000000 : ℚ) : ℝ) ≤ stT317 208 := by
  have hc : ((511399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2836730253/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((511399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c209 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-104053/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6385659/10000000) (δ := 1587/100000000) (ψ := 394423/500000) 317 269
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t209 : ((-28793466933/500000000000 : ℚ) : ℝ) ≤ stT317 209 := by
  have hc : ((-208131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28793466933/500000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-208131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c210 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-60119/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692433/1250000) (δ := 15863/1000000000) (ψ := 394423/500000) 317 270
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t210 : ((-20746489257/500000000000 : ℚ) : ℝ) ≤ stT317 210 := by
  have hc : ((-60129/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20746489257/500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-60129/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c211 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((758463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1774613/10000000) (δ := 401/25000000) (ψ := 394423/500000) 317 270
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t211 : ((130519580841/2500000000000 : ℚ) : ℝ) ≤ stT317 211 := by
  have hc : ((758363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130519580841/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((758363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c212 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((352291/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 986203/5000000) (δ := 797/50000000) (ψ := 394423/500000) 317 270
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t212 : ((120959911641/2500000000000 : ℚ) : ℝ) ≤ stT317 212 := by
  have hc : ((352241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120959911641/2500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((352241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c213 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-325893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 712729/1250000) (δ := 401/25000000) (ψ := 394423/500000) 317 270
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t213 : ((-223332558227/5000000000000 : ℚ) : ℝ) ≤ stT317 213 := by
  have hc : ((-325943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223332558227/5000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-325943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c214 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-162317/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6294141/10000000) (δ := 991/62500000) (ψ := 394423/500000) 317 271
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t214 : ((-55485650241/1000000000000 : ℚ) : ℝ) ≤ stT317 214 := by
  have hc : ((-162337/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55485650241/1000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-162337/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c215 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((506391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1299753/5000000) (δ := 991/62500000) (ψ := 394423/500000) 317 271
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t215 : ((172643712127/5000000000000 : ℚ) : ℝ) ≤ stT317 215 := by
  have hc : ((506291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172643712127/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((506291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c216 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((908463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1078011/10000000) (δ := 991/62500000) (ψ := 394423/500000) 317 271
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t216 : ((618061993919/10000000000000 : ℚ) : ℝ) ≤ stT317 216 := by
  have hc : ((908363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((618061993919/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((908363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c217 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-318929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4738489/10000000) (δ := 3989/250000000) (ψ := 394423/500000) 317 271
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t217 : ((-43314248301/2000000000000 : ℚ) : ℝ) ≤ stT317 217 := by
  have hc : ((-319029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43314248301/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-319029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c218 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-195553/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7325797/10000000) (δ := 15949/1000000000) (ψ := 394423/500000) 317 272
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t218 : ((-66229427439/1000000000000 : ℚ) : ℝ) ≤ stT317 218 := by
  have hc : ((-195573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66229427439/1000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-195573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c219 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((18233/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1849381/5000000) (δ := 7927/500000000) (ψ := 394423/500000) 317 272
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t219 : ((12307197981/2000000000000 : ℚ) : ℝ) ≤ stT317 219 := by
  have hc : ((18213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12307197981/2000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((18213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c220 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((62461/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88291/10000000) (δ := 16049/1000000000) (ψ := 394423/500000) 317 272
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t220 : ((168427719981/2500000000000 : ℚ) : ℝ) ≤ stT317 220 := by
  have hc : ((249819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168427719981/2500000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((249819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c221 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((167659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701171/2000000) (δ := 16049/1000000000) (ψ := 394423/500000) 317 272
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t221 : ((3522257739/312500000000 : ℚ) : ℝ) ≤ stT317 221 := by
  have hc : ((167559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3522257739/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((167559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c222 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-190581/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1770919/2500000) (δ := 7927/500000000) (ψ := 394423/500000) 317 272
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t222 : ((-127923195357/2000000000000 : ℚ) : ℝ) ≤ stT317 222 := by
  have hc : ((-190601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127923195357/2000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-190601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c223 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-219369/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -202499/400000) (δ := 7981/500000000) (ψ := 394423/500000) 317 273
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t223 : ((-2938678667/100000000000 : ℚ) : ℝ) ≤ stT317 223 := by
  have hc : ((-219419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2938678667/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-219419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c224 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((82157/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1516593/10000000) (δ := 16041/1000000000) (ψ := 394423/500000) 317 273
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t224 : ((54886764491/1000000000000 : ℚ) : ℝ) ≤ stT317 224 := by
  have hc : ((82147/100000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54886764491/1000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((82147/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c225 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((692817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2013519/10000000) (δ := 16041/1000000000) (ψ := 394423/500000) 317 273
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t225 : ((230905435761/5000000000000 : ℚ) : ℝ) ≤ stT317 225 := by
  have hc : ((692717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230905435761/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((692717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c226 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-597487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55279/100000) (δ := 31841/1000000000) (ψ := 394423/500000) 317 273
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t226 : ((-397509494117/10000000000000 : ℚ) : ℝ) ≤ stT317 226 := by
  have hc : ((-597587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397509494117/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-597587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c227 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-445979/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417571/625000) (δ := 7967/500000000) (ψ := 394423/500000) 317 274
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t227 : ((-74010037999/1250000000000 : ℚ) : ℝ) ≤ stT317 227 := by
  have hc : ((-446029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74010037999/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-446029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c228 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((143813/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3197623/10000000) (δ := 7967/500000000) (ψ := 394423/500000) 317 274
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t228 : ((47604673479/2500000000000 : ℚ) : ℝ) ≤ stT317 228 := by
  have hc : ((143763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47604673479/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((143763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c229 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((198829/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135337/5000000) (δ := 7967/500000000) (ψ := 394423/500000) 317 274
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t229 : ((65688282881/1000000000000 : ℚ) : ℝ) ≤ stT317 229 := by
  have hc : ((198809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65688282881/1000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((198809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c230 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((81173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1861917/5000000) (δ := 8017/500000000) (ψ := 394423/500000) 317 274
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t230 : ((2672895737/500000000000 : ℚ) : ℝ) ≤ stT317 230 := by
  have hc : ((81073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2672895737/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((81073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c231 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-961939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223813/312500) (δ := 8017/500000000) (ψ := 394423/500000) 317 274
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t231 : ((-19780483879/312500000000 : ℚ) : ℝ) ≤ stT317 231 := by
  have hc : ((-962039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19780483879/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-962039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c232 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-460243/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -640333/1250000) (δ := 15927/1000000000) (ψ := 394423/500000) 317 275
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t232 : ((-302230370819/10000000000000 : ℚ) : ℝ) ≤ stT317 232 := by
  have hc : ((-460343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302230370819/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-460343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c233 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((774029/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857021/5000000) (δ := 3969/250000000) (ψ := 394423/500000) 317 275
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t233 : ((507017140409/10000000000000 : ℚ) : ℝ) ≤ stT317 233 := by
  have hc : ((773929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507017140409/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((773929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c234 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((782579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 839999/5000000) (δ := 1997/125000000) (ψ := 394423/500000) 317 275
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t234 : ((12788054297/250000000000 : ℚ) : ℝ) ≤ stT317 234 := by
  have hc : ((782479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12788054297/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((782479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c235 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-437681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1011907/2000000) (δ := 1997/125000000) (ψ := 394423/500000) 317 275
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t235 : ((-285577241949/10000000000000 : ℚ) : ℝ) ≤ stT317 235 := by
  have hc : ((-437781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285577241949/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-437781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c236 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-974053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1820809/2500000) (δ := 199/12500000) (ψ := 394423/500000) 317 276
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t236 : ((-126824004917/2000000000000 : ℚ) : ℝ) ≤ stT317 236 := by
  have hc : ((-974153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126824004917/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-974153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c237 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-2127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -983077/2500000) (δ := 15883/1000000000) (ψ := 394423/500000) 317 276
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t237 : ((-144659239/1000000000000 : ℚ) : ℝ) ≤ stT317 237 := by
  have hc : ((-2227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144659239/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-2227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c238 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((194353/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595487/10000000) (δ := 199/12500000) (ψ := 394423/500000) 317 276
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t238 : ((125967233599/2000000000000 : ℚ) : ℝ) ≤ stT317 238 := by
  have hc : ((194333/200000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125967233599/2000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((194333/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c239 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((461639/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1363693/5000000) (δ := 801/50000000) (ψ := 394423/500000) 317 276
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t239 : ((149272327997/5000000000000 : ℚ) : ℝ) ≤ stT317 239 := by
  have hc : ((461539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149272327997/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((461539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c240 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-186787/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6036391/10000000) (δ := 15883/1000000000) (ψ := 394423/500000) 317 276
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t240 : ((-15073346547/312500000000 : ℚ) : ℝ) ≤ stT317 240 := by
  have hc : ((-46703/62500 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15073346547/312500000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-46703/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c241 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-207589/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6376357/10000000) (δ := 1599/100000000) (ψ := 394423/500000) 317 277
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t241 : ((-66868005699/1250000000000 : ℚ) : ℝ) ≤ stT317 241 := by
  have hc : ((-103807/125000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66868005699/1250000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-103807/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c242 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((326773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3094773/10000000) (δ := 1599/100000000) (ψ := 394423/500000) 317 277
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t242 : ((26249155569/1250000000000 : ℚ) : ℝ) ≤ stT317 242 := by
  have hc : ((326673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26249155569/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((326673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c243 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((997599/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173259/10000000) (δ := 1589/100000000) (ψ := 394423/500000) 317 277
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t243 : ((1279791217/20000000000 : ℚ) : ℝ) ≤ stT317 243 := by
  have hc : ((997499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1279791217/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((997499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c244 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((99157/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1713949/5000000) (δ := 1589/100000000) (ψ := 394423/500000) 317 277
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t244 : ((7930839461/625000000000 : ℚ) : ℝ) ≤ stT317 244 := by
  have hc : ((99107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7930839461/625000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((99107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c245 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-444893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6669183/10000000) (δ := 31813/1000000000) (ψ := 394423/500000) 317 277
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t245 : ((-284263849011/5000000000000 : ℚ) : ℝ) ≤ stT317 245 := by
  have hc : ((-444943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284263849011/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-444943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c246 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-684169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116213/200000) (δ := 15897/1000000000) (ψ := 394423/500000) 317 278
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t246 : ((-436274176213/10000000000000 : ℚ) : ℝ) ≤ stT317 246 := by
  have hc : ((-684269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436274176213/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-684269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c247 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((20309/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -648909/2500000) (δ := 15897/1000000000) (ψ := 394423/500000) 317 278
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t247 : ((645987331/20000000000 : ℚ) : ℝ) ≤ stT317 247 := by
  have hc : ((4061/8000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((645987331/20000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((4061/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c248 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((121341/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606381/10000000) (δ := 15897/1000000000) (ψ := 394423/500000) 317 278
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t248 : ((30817439/500000000 : ℚ) : ℝ) ≤ stT317 248 := by
  have hc : ((242657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30817439/500000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((242657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c249 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((2629/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94887/250000) (δ := 7953/500000000) (ψ := 394423/500000) 317 278
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t249 : ((6495671/1953125000 : ℚ) : ℝ) ≤ stT317 249 := by
  have hc : ((164/3125 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6495671/1953125000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((164/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_c250 :
    |Real.cos (((317 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((-938397/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6971899/10000000) (δ := 8003/500000000) (ψ := 394423/500000) 317 278
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st317_t250 : ((-74194757329/1250000000000 : ℚ) : ℝ) ≤ stT317 250 := by
  have hc : ((-938497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((317 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((394423/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st317_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74194757329/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-938497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st317_p1 : ((140913/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT317 (i+1) := by
  rw [Finset.sum_range_one]
  exact st317_t1

theorem st317_p2 : ((11026540512861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT317 (i+1))
      = (∑ i ∈ Finset.range 1, stT317 (i+1)) + stT317 2 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 1
    simpa using h
  have hprev := st317_p1
  have hstep := st317_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p3 : ((4590534573213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT317 (i+1))
      = (∑ i ∈ Finset.range 2, stT317 (i+1)) + stT317 3 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 2
    simpa using h
  have hprev := st317_p2
  have hstep := st317_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p4 : ((5596629573213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT317 (i+1))
      = (∑ i ∈ Finset.range 3, stT317 (i+1)) + stT317 4 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 3
    simpa using h
  have hprev := st317_p3
  have hstep := st317_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p5 : ((15190153776381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT317 (i+1))
      = (∑ i ∈ Finset.range 4, stT317 (i+1)) + stT317 5 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 4
    simpa using h
  have hprev := st317_p4
  have hstep := st317_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p6 : ((913393696051/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT317 (i+1))
      = (∑ i ∈ Finset.range 5, stT317 (i+1)) + stT317 6 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 5
    simpa using h
  have hprev := st317_p5
  have hstep := st317_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p7 : ((1138155895977/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT317 (i+1))
      = (∑ i ∈ Finset.range 6, stT317 (i+1)) + stT317 7 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 6
    simpa using h
  have hprev := st317_p6
  have hstep := st317_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p8 : ((9508881292761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT317 (i+1))
      = (∑ i ∈ Finset.range 7, stT317 (i+1)) + stT317 8 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 7
    simpa using h
  have hprev := st317_p7
  have hstep := st317_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p9 : ((74322276659/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT317 (i+1))
      = (∑ i ∈ Finset.range 8, stT317 (i+1)) + stT317 9 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 8
    simpa using h
  have hprev := st317_p8
  have hstep := st317_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p10 : ((5404599478923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT317 (i+1))
      = (∑ i ∈ Finset.range 9, stT317 (i+1)) + stT317 10 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 9
    simpa using h
  have hprev := st317_p9
  have hstep := st317_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p11 : ((23441175434503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT317 (i+1))
      = (∑ i ∈ Finset.range 10, stT317 (i+1)) + stT317 11 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 10
    simpa using h
  have hprev := st317_p10
  have hstep := st317_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p12 : ((11781620850269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT317 (i+1))
      = (∑ i ∈ Finset.range 11, stT317 (i+1)) + stT317 12 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 11
    simpa using h
  have hprev := st317_p11
  have hstep := st317_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p13 : ((1150815642517/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT317 (i+1))
      = (∑ i ∈ Finset.range 12, stT317 (i+1)) + stT317 13 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 12
    simpa using h
  have hprev := st317_p12
  have hstep := st317_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p14 : ((25064997813/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT317 (i+1))
      = (∑ i ∈ Finset.range 13, stT317 (i+1)) + stT317 14 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 13
    simpa using h
  have hprev := st317_p13
  have hstep := st317_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p15 : ((11542199174619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT317 (i+1))
      = (∑ i ∈ Finset.range 14, stT317 (i+1)) + stT317 15 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 14
    simpa using h
  have hprev := st317_p14
  have hstep := st317_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p16 : ((11600354174619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT317 (i+1))
      = (∑ i ∈ Finset.range 15, stT317 (i+1)) + stT317 16 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 15
    simpa using h
  have hprev := st317_p15
  have hstep := st317_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p17 : ((12089264713167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT317 (i+1))
      = (∑ i ∈ Finset.range 16, stT317 (i+1)) + stT317 17 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 16
    simpa using h
  have hprev := st317_p16
  have hstep := st317_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p18 : ((4689493620317/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT317 (i+1))
      = (∑ i ∈ Finset.range 17, stT317 (i+1)) + stT317 18 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 17
    simpa using h
  have hprev := st317_p17
  have hstep := st317_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p19 : ((4277240310191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT317 (i+1))
      = (∑ i ∈ Finset.range 18, stT317 (i+1)) + stT317 19 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 18
    simpa using h
  have hprev := st317_p18
  have hstep := st317_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p20 : ((4722293669469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT317 (i+1))
      = (∑ i ∈ Finset.range 19, stT317 (i+1)) + stT317 20 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 19
    simpa using h
  have hprev := st317_p19
  have hstep := st317_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p21 : ((2145171123657/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT317 (i+1))
      = (∑ i ∈ Finset.range 20, stT317 (i+1)) + stT317 21 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 20
    simpa using h
  have hprev := st317_p20
  have hstep := st317_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p22 : ((22408489885953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT317 (i+1))
      = (∑ i ∈ Finset.range 21, stT317 (i+1)) + stT317 22 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 21
    simpa using h
  have hprev := st317_p21
  have hstep := st317_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p23 : ((24312582917577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT317 (i+1))
      = (∑ i ∈ Finset.range 22, stT317 (i+1)) + stT317 23 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 22
    simpa using h
  have hprev := st317_p22
  have hstep := st317_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p24 : ((12385111513027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT317 (i+1))
      = (∑ i ∈ Finset.range 23, stT317 (i+1)) + stT317 24 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 23
    simpa using h
  have hprev := st317_p23
  have hstep := st317_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p25 : ((24475136878511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT317 (i+1))
      = (∑ i ∈ Finset.range 24, stT317 (i+1)) + stT317 25 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 24
    simpa using h
  have hprev := st317_p24
  have hstep := st317_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p26 : ((4889272149697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT317 (i+1))
      = (∑ i ∈ Finset.range 25, stT317 (i+1)) + stT317 26 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 25
    simpa using h
  have hprev := st317_p25
  have hstep := st317_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p27 : ((5102775794797/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT317 (i+1))
      = (∑ i ∈ Finset.range 26, stT317 (i+1)) + stT317 27 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 26
    simpa using h
  have hprev := st317_p26
  have hstep := st317_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p28 : ((5480127892469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT317 (i+1))
      = (∑ i ∈ Finset.range 27, stT317 (i+1)) + stT317 28 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 27
    simpa using h
  have hprev := st317_p27
  have hstep := st317_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p29 : ((6884080361799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT317 (i+1))
      = (∑ i ∈ Finset.range 28, stT317 (i+1)) + stT317 29 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 28
    simpa using h
  have hprev := st317_p28
  have hstep := st317_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p30 : ((1286923108951/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT317 (i+1))
      = (∑ i ∈ Finset.range 29, stT317 (i+1)) + stT317 30 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 29
    simpa using h
  have hprev := st317_p29
  have hstep := st317_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p31 : ((134986219423/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT317 (i+1))
      = (∑ i ∈ Finset.range 30, stT317 (i+1)) + stT317 31 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 30
    simpa using h
  have hprev := st317_p30
  have hstep := st317_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p32 : ((26755319667349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT317 (i+1))
      = (∑ i ∈ Finset.range 31, stT317 (i+1)) + stT317 32 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 31
    simpa using h
  have hprev := st317_p31
  have hstep := st317_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p33 : ((26421877314553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT317 (i+1))
      = (∑ i ∈ Finset.range 32, stT317 (i+1)) + stT317 33 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 32
    simpa using h
  have hprev := st317_p32
  have hstep := st317_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p34 : ((26814787237993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT317 (i+1))
      = (∑ i ∈ Finset.range 33, stT317 (i+1)) + stT317 34 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 33
    simpa using h
  have hprev := st317_p33
  have hstep := st317_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p35 : ((26822190787033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT317 (i+1))
      = (∑ i ∈ Finset.range 34, stT317 (i+1)) + stT317 35 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 34
    simpa using h
  have hprev := st317_p34
  have hstep := st317_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p36 : ((13012161147063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT317 (i+1))
      = (∑ i ∈ Finset.range 35, stT317 (i+1)) + stT317 36 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 35
    simpa using h
  have hprev := st317_p35
  have hstep := st317_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p37 : ((2757814836141/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT317 (i+1))
      = (∑ i ∈ Finset.range 36, stT317 (i+1)) + stT317 37 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 36
    simpa using h
  have hprev := st317_p36
  have hstep := st317_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p38 : ((5255080205601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT317 (i+1))
      = (∑ i ∈ Finset.range 37, stT317 (i+1)) + stT317 38 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 37
    simpa using h
  have hprev := st317_p37
  have hstep := st317_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p39 : ((25866231843673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT317 (i+1))
      = (∑ i ∈ Finset.range 38, stT317 (i+1)) + stT317 39 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 38
    simpa using h
  have hprev := st317_p38
  have hstep := st317_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p40 : ((5488259338523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT317 (i+1))
      = (∑ i ∈ Finset.range 39, stT317 (i+1)) + stT317 40 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 39
    simpa using h
  have hprev := st317_p39
  have hstep := st317_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p41 : ((2761717170487/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT317 (i+1))
      = (∑ i ∈ Finset.range 40, stT317 (i+1)) + stT317 41 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 40
    simpa using h
  have hprev := st317_p40
  have hstep := st317_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p42 : ((6539061021761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT317 (i+1))
      = (∑ i ∈ Finset.range 41, stT317 (i+1)) + stT317 42 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 41
    simpa using h
  have hprev := st317_p41
  have hstep := st317_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p43 : ((12573660487187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT317 (i+1))
      = (∑ i ∈ Finset.range 42, stT317 (i+1)) + stT317 43 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 42
    simpa using h
  have hprev := st317_p42
  have hstep := st317_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p44 : ((2556621952987/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT317 (i+1))
      = (∑ i ∈ Finset.range 43, stT317 (i+1)) + stT317 44 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 43
    simpa using h
  have hprev := st317_p43
  have hstep := st317_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p45 : ((134546974311/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT317 (i+1))
      = (∑ i ∈ Finset.range 44, stT317 (i+1)) + stT317 45 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 44
    simpa using h
  have hprev := st317_p44
  have hstep := st317_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p46 : ((7085725420947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT317 (i+1))
      = (∑ i ∈ Finset.range 45, stT317 (i+1)) + stT317 46 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 45
    simpa using h
  have hprev := st317_p45
  have hstep := st317_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p47 : ((3673740721323/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT317 (i+1))
      = (∑ i ∈ Finset.range 46, stT317 (i+1)) + stT317 47 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 46
    simpa using h
  have hprev := st317_p46
  have hstep := st317_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p48 : ((14982591438417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT317 (i+1))
      = (∑ i ∈ Finset.range 47, stT317 (i+1)) + stT317 48 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 47
    simpa using h
  have hprev := st317_p47
  have hstep := st317_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p49 : ((15094162833517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT317 (i+1))
      = (∑ i ∈ Finset.range 48, stT317 (i+1)) + stT317 49 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 48
    simpa using h
  have hprev := st317_p48
  have hstep := st317_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p50 : ((30238859740163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT317 (i+1))
      = (∑ i ∈ Finset.range 49, stT317 (i+1)) + stT317 50 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 49
    simpa using h
  have hprev := st317_p49
  have hstep := st317_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p51 : ((30296957357363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT317 (i+1))
      = (∑ i ∈ Finset.range 50, stT317 (i+1)) + stT317 51 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 50
    simpa using h
  have hprev := st317_p50
  have hstep := st317_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p52 : ((30530407012613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT317 (i+1))
      = (∑ i ∈ Finset.range 51, stT317 (i+1)) + stT317 52 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 51
    simpa using h
  have hprev := st317_p51
  have hstep := st317_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p53 : ((15541515827699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT317 (i+1))
      = (∑ i ∈ Finset.range 52, stT317 (i+1)) + stT317 53 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 52
    simpa using h
  have hprev := st317_p52
  have hstep := st317_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p54 : ((4004014153751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT317 (i+1))
      = (∑ i ∈ Finset.range 53, stT317 (i+1)) + stT317 54 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 53
    simpa using h
  have hprev := st317_p53
  have hstep := st317_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p55 : ((33306599738823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT317 (i+1))
      = (∑ i ∈ Finset.range 54, stT317 (i+1)) + stT317 55 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 54
    simpa using h
  have hprev := st317_p54
  have hstep := st317_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p56 : ((6920958056557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT317 (i+1))
      = (∑ i ∈ Finset.range 55, stT317 (i+1)) + stT317 56 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 55
    simpa using h
  have hprev := st317_p55
  have hstep := st317_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p57 : ((35416116465001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT317 (i+1))
      = (∑ i ∈ Finset.range 56, stT317 (i+1)) + stT317 57 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 56
    simpa using h
  have hprev := st317_p56
  have hstep := st317_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p58 : ((35271067426711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT317 (i+1))
      = (∑ i ∈ Finset.range 57, stT317 (i+1)) + stT317 58 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 57
    simpa using h
  have hprev := st317_p57
  have hstep := st317_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p59 : ((34193469639691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT317 (i+1))
      = (∑ i ∈ Finset.range 58, stT317 (i+1)) + stT317 59 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 58
    simpa using h
  have hprev := st317_p58
  have hstep := st317_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p60 : ((32984824628751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT317 (i+1))
      = (∑ i ∈ Finset.range 59, stT317 (i+1)) + stT317 60 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 59
    simpa using h
  have hprev := st317_p59
  have hstep := st317_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p61 : ((32770593287671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT317 (i+1))
      = (∑ i ∈ Finset.range 60, stT317 (i+1)) + stT317 61 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 60
    simpa using h
  have hprev := st317_p60
  have hstep := st317_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p62 : ((6762255057421/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT317 (i+1))
      = (∑ i ∈ Finset.range 61, stT317 (i+1)) + stT317 62 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 61
    simpa using h
  have hprev := st317_p61
  have hstep := st317_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p63 : ((6970072428371/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT317 (i+1))
      = (∑ i ∈ Finset.range 62, stT317 (i+1)) + stT317 63 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 62
    simpa using h
  have hprev := st317_p62
  have hstep := st317_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p64 : ((8613949519051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT317 (i+1))
      = (∑ i ∈ Finset.range 63, stT317 (i+1)) + stT317 64 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 63
    simpa using h
  have hprev := st317_p63
  have hstep := st317_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p65 : ((8306009561439/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT317 (i+1))
      = (∑ i ∈ Finset.range 64, stT317 (i+1)) + stT317 65 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 64
    simpa using h
  have hprev := st317_p64
  have hstep := st317_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p66 : ((16606532934723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT317 (i+1))
      = (∑ i ∈ Finset.range 65, stT317 (i+1)) + stT317 66 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 65
    simpa using h
  have hprev := st317_p65
  have hstep := st317_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p67 : ((17216089825859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT317 (i+1))
      = (∑ i ∈ Finset.range 66, stT317 (i+1)) + stT317 67 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 66
    simpa using h
  have hprev := st317_p66
  have hstep := st317_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p68 : ((17244781181/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT317 (i+1))
      = (∑ i ∈ Finset.range 67, stT317 (i+1)) + stT317 68 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 67
    simpa using h
  have hprev := st317_p67
  have hstep := st317_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p69 : ((33286412434951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT317 (i+1))
      = (∑ i ∈ Finset.range 68, stT317 (i+1)) + stT317 69 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 68
    simpa using h
  have hprev := st317_p68
  have hstep := st317_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p70 : ((6702006245431/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT317 (i+1))
      = (∑ i ∈ Finset.range 69, stT317 (i+1)) + stT317 70 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 69
    simpa using h
  have hprev := st317_p69
  have hstep := st317_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p71 : ((17300535521771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT317 (i+1))
      = (∑ i ∈ Finset.range 70, stT317 (i+1)) + stT317 71 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 70
    simpa using h
  have hprev := st317_p70
  have hstep := st317_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p72 : ((16928626597371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT317 (i+1))
      = (∑ i ∈ Finset.range 71, stT317 (i+1)) + stT317 72 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 71
    simpa using h
  have hprev := st317_p71
  have hstep := st317_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p73 : ((3324739714761/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT317 (i+1))
      = (∑ i ∈ Finset.range 72, stT317 (i+1)) + stT317 73 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 72
    simpa using h
  have hprev := st317_p72
  have hstep := st317_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p74 : ((3439695222687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT317 (i+1))
      = (∑ i ∈ Finset.range 73, stT317 (i+1)) + stT317 74 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 73
    simpa using h
  have hprev := st317_p73
  have hstep := st317_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p75 : ((34046012034847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT317 (i+1))
      = (∑ i ∈ Finset.range 74, stT317 (i+1)) + stT317 75 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 74
    simpa using h
  have hprev := st317_p74
  have hstep := st317_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p76 : ((16632660195579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT317 (i+1))
      = (∑ i ∈ Finset.range 75, stT317 (i+1)) + stT317 76 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 75
    simpa using h
  have hprev := st317_p75
  have hstep := st317_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p77 : ((2149151280323/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT317 (i+1))
      = (∑ i ∈ Finset.range 76, stT317 (i+1)) + stT317 77 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 76
    simpa using h
  have hprev := st317_p76
  have hstep := st317_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p78 : ((16950931623673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT317 (i+1))
      = (∑ i ∈ Finset.range 77, stT317 (i+1)) + stT317 78 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 77
    simpa using h
  have hprev := st317_p77
  have hstep := st317_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p79 : ((16703881425369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT317 (i+1))
      = (∑ i ∈ Finset.range 78, stT317 (i+1)) + stT317 79 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 78
    simpa using h
  have hprev := st317_p78
  have hstep := st317_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p80 : ((34485073734779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT317 (i+1))
      = (∑ i ∈ Finset.range 79, stT317 (i+1)) + stT317 80 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 79
    simpa using h
  have hprev := st317_p79
  have hstep := st317_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p81 : ((33524041854843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT317 (i+1))
      = (∑ i ∈ Finset.range 80, stT317 (i+1)) + stT317 81 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 80
    simpa using h
  have hprev := st317_p80
  have hstep := st317_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p82 : ((16923439203129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT317 (i+1))
      = (∑ i ∈ Finset.range 81, stT317 (i+1)) + stT317 82 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 81
    simpa using h
  have hprev := st317_p81
  have hstep := st317_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p83 : ((4284795596173/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT317 (i+1))
      = (∑ i ∈ Finset.range 82, stT317 (i+1)) + stT317 83 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 82
    simpa using h
  have hprev := st317_p82
  have hstep := st317_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p84 : ((8331748302061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT317 (i+1))
      = (∑ i ∈ Finset.range 83, stT317 (i+1)) + stT317 84 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 83
    simpa using h
  have hprev := st317_p83
  have hstep := st317_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p85 : ((430079035261/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT317 (i+1))
      = (∑ i ∈ Finset.range 84, stT317 (i+1)) + stT317 85 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 84
    simpa using h
  have hprev := st317_p84
  have hstep := st317_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p86 : ((4194635296187/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT317 (i+1))
      = (∑ i ∈ Finset.range 85, stT317 (i+1)) + stT317 86 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 85
    simpa using h
  have hprev := st317_p85
  have hstep := st317_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p87 : ((4244759882537/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT317 (i+1))
      = (∑ i ∈ Finset.range 86, stT317 (i+1)) + stT317 87 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 86
    simpa using h
  have hprev := st317_p86
  have hstep := st317_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p88 : ((8515529172271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT317 (i+1))
      = (∑ i ∈ Finset.range 87, stT317 (i+1)) + stT317 88 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 87
    simpa using h
  have hprev := st317_p87
  have hstep := st317_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p89 : ((8379666048617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT317 (i+1))
      = (∑ i ∈ Finset.range 88, stT317 (i+1)) + stT317 89 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 88
    simpa using h
  have hprev := st317_p88
  have hstep := st317_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p90 : ((4296111718447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT317 (i+1))
      = (∑ i ∈ Finset.range 89, stT317 (i+1)) + stT317 90 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 89
    simpa using h
  have hprev := st317_p89
  have hstep := st317_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p91 : ((2084923419241/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT317 (i+1))
      = (∑ i ∈ Finset.range 90, stT317 (i+1)) + stT317 91 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 90
    simpa using h
  have hprev := st317_p90
  have hstep := st317_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p92 : ((8599960047829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT317 (i+1))
      = (∑ i ∈ Finset.range 91, stT317 (i+1)) + stT317 92 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 91
    simpa using h
  have hprev := st317_p91
  have hstep := st317_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p93 : ((8355307036947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT317 (i+1))
      = (∑ i ∈ Finset.range 92, stT317 (i+1)) + stT317 93 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 92
    simpa using h
  have hprev := st317_p92
  have hstep := st317_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p94 : ((17140187511921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT317 (i+1))
      = (∑ i ∈ Finset.range 93, stT317 (i+1)) + stT317 94 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 93
    simpa using h
  have hprev := st317_p93
  have hstep := st317_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p95 : ((33564794684523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT317 (i+1))
      = (∑ i ∈ Finset.range 94, stT317 (i+1)) + stT317 95 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 94
    simpa using h
  have hprev := st317_p94
  have hstep := st317_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p96 : ((34135828512663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT317 (i+1))
      = (∑ i ∈ Finset.range 95, stT317 (i+1)) + stT317 96 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 95
    simpa using h
  have hprev := st317_p95
  have hstep := st317_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p97 : ((33693642863469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT317 (i+1))
      = (∑ i ∈ Finset.range 96, stT317 (i+1)) + stT317 97 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 96
    simpa using h
  have hprev := st317_p96
  have hstep := st317_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p98 : ((34031144748189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT317 (i+1))
      = (∑ i ∈ Finset.range 97, stT317 (i+1)) + stT317 98 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 97
    simpa using h
  have hprev := st317_p97
  have hstep := st317_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p99 : ((33768738371731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT317 (i+1))
      = (∑ i ∈ Finset.range 98, stT317 (i+1)) + stT317 99 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 98
    simpa using h
  have hprev := st317_p98
  have hstep := st317_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p100 : ((16993285576949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT317 (i+1))
      = (∑ i ∈ Finset.range 99, stT317 (i+1)) + stT317 100 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 99
    simpa using h
  have hprev := st317_p99
  have hstep := st317_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p101 : ((8445488631173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT317 (i+1))
      = (∑ i ∈ Finset.range 100, stT317 (i+1)) + stT317 101 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 100
    simpa using h
  have hprev := st317_p100
  have hstep := st317_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p102 : ((34003174157579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT317 (i+1))
      = (∑ i ∈ Finset.range 101, stT317 (i+1)) + stT317 102 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 101
    simpa using h
  have hprev := st317_p101
  have hstep := st317_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p103 : ((33736143815599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT317 (i+1))
      = (∑ i ∈ Finset.range 102, stT317 (i+1)) + stT317 103 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 102
    simpa using h
  have hprev := st317_p102
  have hstep := st317_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p104 : ((34075143069139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT317 (i+1))
      = (∑ i ∈ Finset.range 103, stT317 (i+1)) + stT317 104 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 103
    simpa using h
  have hprev := st317_p103
  have hstep := st317_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p105 : ((16820388182673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT317 (i+1))
      = (∑ i ∈ Finset.range 104, stT317 (i+1)) + stT317 105 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 104
    simpa using h
  have hprev := st317_p104
  have hstep := st317_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p106 : ((17093756345923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT317 (i+1))
      = (∑ i ∈ Finset.range 105, stT317 (i+1)) + stT317 106 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 105
    simpa using h
  have hprev := st317_p105
  have hstep := st317_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p107 : ((16759642371353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT317 (i+1))
      = (∑ i ∈ Finset.range 106, stT317 (i+1)) + stT317 107 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 106
    simpa using h
  have hprev := st317_p106
  have hstep := st317_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p108 : ((17152556951603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT317 (i+1))
      = (∑ i ∈ Finset.range 107, stT317 (i+1)) + stT317 108 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 107
    simpa using h
  have hprev := st317_p107
  have hstep := st317_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p109 : ((33420983070413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT317 (i+1))
      = (∑ i ∈ Finset.range 108, stT317 (i+1)) + stT317 109 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 108
    simpa using h
  have hprev := st317_p108
  have hstep := st317_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p110 : ((34363854967979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT317 (i+1))
      = (∑ i ∈ Finset.range 109, stT317 (i+1)) + stT317 110 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 109
    simpa using h
  have hprev := st317_p109
  have hstep := st317_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p111 : ((33421921009517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT317 (i+1))
      = (∑ i ∈ Finset.range 110, stT317 (i+1)) + stT317 111 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 110
    simpa using h
  have hprev := st317_p110
  have hstep := st317_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p112 : ((6856705353187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT317 (i+1))
      = (∑ i ∈ Finset.range 111, stT317 (i+1)) + stT317 112 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 111
    simpa using h
  have hprev := st317_p111
  have hstep := st317_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p113 : ((8398234223697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT317 (i+1))
      = (∑ i ∈ Finset.range 112, stT317 (i+1)) + stT317 113 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 112
    simpa using h
  have hprev := st317_p112
  have hstep := st317_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p114 : ((17010827466099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT317 (i+1))
      = (∑ i ∈ Finset.range 113, stT317 (i+1)) + stT317 114 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 113
    simpa using h
  have hprev := st317_p113
  have hstep := st317_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p115 : ((33926090887293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT317 (i+1))
      = (∑ i ∈ Finset.range 114, stT317 (i+1)) + stT317 115 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 114
    simpa using h
  have hprev := st317_p114
  have hstep := st317_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p116 : ((336565456579/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT317 (i+1))
      = (∑ i ∈ Finset.range 115, stT317 (i+1)) + stT317 116 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 115
    simpa using h
  have hprev := st317_p115
  have hstep := st317_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p117 : ((342625535589/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT317 (i+1))
      = (∑ i ∈ Finset.range 116, stT317 (i+1)) + stT317 117 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 116
    simpa using h
  have hprev := st317_p116
  have hstep := st317_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p118 : ((1336758539377/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT317 (i+1))
      = (∑ i ∈ Finset.range 117, stT317 (i+1)) + stT317 118 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 117
    simpa using h
  have hprev := st317_p117
  have hstep := st317_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p119 : ((34334214934981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT317 (i+1))
      = (∑ i ∈ Finset.range 118, stT317 (i+1)) + stT317 119 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 118
    simpa using h
  have hprev := st317_p118
  have hstep := st317_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p120 : ((33552658602589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT317 (i+1))
      = (∑ i ∈ Finset.range 119, stT317 (i+1)) + stT317 120 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 119
    simpa using h
  have hprev := st317_p119
  have hstep := st317_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p121 : ((34001679062659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT317 (i+1))
      = (∑ i ∈ Finset.range 120, stT317 (i+1)) + stT317 121 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 120
    simpa using h
  have hprev := st317_p120
  have hstep := st317_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p122 : ((85039762343/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT317 (i+1))
      = (∑ i ∈ Finset.range 121, stT317 (i+1)) + stT317 122 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 121
    simpa using h
  have hprev := st317_p121
  have hstep := st317_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p123 : ((3352951799077/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT317 (i+1))
      = (∑ i ∈ Finset.range 122, stT317 (i+1)) + stT317 123 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 122
    simpa using h
  have hprev := st317_p122
  have hstep := st317_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p124 : ((2146690926151/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT317 (i+1))
      = (∑ i ∈ Finset.range 123, stT317 (i+1)) + stT317 124 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 123
    simpa using h
  have hprev := st317_p123
  have hstep := st317_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p125 : ((209158007411/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT317 (i+1))
      = (∑ i ∈ Finset.range 124, stT317 (i+1)) + stT317 125 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 124
    simpa using h
  have hprev := st317_p124
  have hstep := st317_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p126 : ((85238956003/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT317 (i+1))
      = (∑ i ∈ Finset.range 125, stT317 (i+1)) + stT317 126 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 125
    simpa using h
  have hprev := st317_p125
  have hstep := st317_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p127 : ((33962504584553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT317 (i+1))
      = (∑ i ∈ Finset.range 126, stT317 (i+1)) + stT317 127 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 126
    simpa using h
  have hprev := st317_p126
  have hstep := st317_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p128 : ((33534893879729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT317 (i+1))
      = (∑ i ∈ Finset.range 127, stT317 (i+1)) + stT317 128 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 127
    simpa using h
  have hprev := st317_p127
  have hstep := st317_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p129 : ((34348706141029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT317 (i+1))
      = (∑ i ∈ Finset.range 128, stT317 (i+1)) + stT317 129 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 128
    simpa using h
  have hprev := st317_p128
  have hstep := st317_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p130 : ((4188920156201/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT317 (i+1))
      = (∑ i ∈ Finset.range 129, stT317 (i+1)) + stT317 130 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 129
    simpa using h
  have hprev := st317_p129
  have hstep := st317_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p131 : ((2123272051089/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT317 (i+1))
      = (∑ i ∈ Finset.range 130, stT317 (i+1)) + stT317 131 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 130
    simpa using h
  have hprev := st317_p130
  have hstep := st317_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p132 : ((4265476999551/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT317 (i+1))
      = (∑ i ∈ Finset.range 131, stT317 (i+1)) + stT317 132 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 131
    simpa using h
  have hprev := st317_p131
  have hstep := st317_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p133 : ((16715843096539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT317 (i+1))
      = (∑ i ∈ Finset.range 132, stT317 (i+1)) + stT317 133 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 132
    simpa using h
  have hprev := st317_p132
  have hstep := st317_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p134 : ((17144607132913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT317 (i+1))
      = (∑ i ∈ Finset.range 133, stT317 (i+1)) + stT317 134 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 133
    simpa using h
  have hprev := st317_p133
  have hstep := st317_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p135 : ((16878793086689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT317 (i+1))
      = (∑ i ∈ Finset.range 134, stT317 (i+1)) + stT317 135 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 134
    simpa using h
  have hprev := st317_p134
  have hstep := st317_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p136 : ((672817696121/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT317 (i+1))
      = (∑ i ∈ Finset.range 135, stT317 (i+1)) + stT317 136 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 135
    simpa using h
  have hprev := st317_p135
  have hstep := st317_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p137 : ((1073079292307/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT317 (i+1))
      = (∑ i ∈ Finset.range 136, stT317 (i+1)) + stT317 137 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 136
    simpa using h
  have hprev := st317_p136
  have hstep := st317_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p138 : ((33507896947107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT317 (i+1))
      = (∑ i ∈ Finset.range 137, stT317 (i+1)) + stT317 138 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 137
    simpa using h
  have hprev := st317_p137
  have hstep := st317_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p139 : ((1356490348059/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT317 (i+1))
      = (∑ i ∈ Finset.range 138, stT317 (i+1)) + stT317 139 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 138
    simpa using h
  have hprev := st317_p138
  have hstep := st317_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p140 : ((34219470490167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT317 (i+1))
      = (∑ i ∈ Finset.range 139, stT317 (i+1)) + stT317 140 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 139
    simpa using h
  have hprev := st317_p139
  have hstep := st317_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p141 : ((33418226865719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT317 (i+1))
      = (∑ i ∈ Finset.range 140, stT317 (i+1)) + stT317 141 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 140
    simpa using h
  have hprev := st317_p140
  have hstep := st317_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p142 : ((8529096504053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT317 (i+1))
      = (∑ i ∈ Finset.range 141, stT317 (i+1)) + stT317 142 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 141
    simpa using h
  have hprev := st317_p141
  have hstep := st317_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p143 : ((34061330285821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT317 (i+1))
      = (∑ i ∈ Finset.range 142, stT317 (i+1)) + stT317 143 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 142
    simpa using h
  have hprev := st317_p142
  have hstep := st317_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p144 : ((33426048944263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT317 (i+1))
      = (∑ i ∈ Finset.range 143, stT317 (i+1)) + stT317 144 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 143
    simpa using h
  have hprev := st317_p143
  have hstep := st317_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p145 : ((6846374003543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT317 (i+1))
      = (∑ i ∈ Finset.range 144, stT317 (i+1)) + stT317 145 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 144
    simpa using h
  have hprev := st317_p144
  have hstep := st317_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p146 : ((33937027931761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT317 (i+1))
      = (∑ i ∈ Finset.range 145, stT317 (i+1)) + stT317 146 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 145
    simpa using h
  have hprev := st317_p145
  have hstep := st317_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p147 : ((6692400351311/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT317 (i+1))
      = (∑ i ∈ Finset.range 146, stT317 (i+1)) + stT317 147 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 146
    simpa using h
  have hprev := st317_p146
  have hstep := st317_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p148 : ((34283402276887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT317 (i+1))
      = (∑ i ∈ Finset.range 147, stT317 (i+1)) + stT317 148 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 147
    simpa using h
  have hprev := st317_p147
  have hstep := st317_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p149 : ((6774024698123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT317 (i+1))
      = (∑ i ∈ Finset.range 148, stT317 (i+1)) + stT317 149 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 148
    simpa using h
  have hprev := st317_p148
  have hstep := st317_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p150 : ((16741967961529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT317 (i+1))
      = (∑ i ∈ Finset.range 149, stT317 (i+1)) + stT317 150 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 149
    simpa using h
  have hprev := st317_p149
  have hstep := st317_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p151 : ((17148445302073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT317 (i+1))
      = (∑ i ∈ Finset.range 150, stT317 (i+1)) + stT317 151 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 150
    simpa using h
  have hprev := st317_p150
  have hstep := st317_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p152 : ((16931398479029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT317 (i+1))
      = (∑ i ∈ Finset.range 151, stT317 (i+1)) + stT317 152 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 151
    simpa using h
  have hprev := st317_p151
  have hstep := st317_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p153 : ((8369084659523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT317 (i+1))
      = (∑ i ∈ Finset.range 152, stT317 (i+1)) + stT317 153 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 152
    simpa using h
  have hprev := st317_p152
  have hstep := st317_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p154 : ((8570518402329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT317 (i+1))
      = (∑ i ∈ Finset.range 153, stT317 (i+1)) + stT317 154 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 153
    simpa using h
  have hprev := st317_p153
  have hstep := st317_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p155 : ((4239147244587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT317 (i+1))
      = (∑ i ∈ Finset.range 154, stT317 (i+1)) + stT317 155 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 154
    simpa using h
  have hprev := st317_p154
  have hstep := st317_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p156 : ((33444038359541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT317 (i+1))
      = (∑ i ∈ Finset.range 155, stT317 (i+1)) + stT317 156 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 155
    simpa using h
  have hprev := st317_p155
  have hstep := st317_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p157 : ((34230382120223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT317 (i+1))
      = (∑ i ∈ Finset.range 156, stT317 (i+1)) + stT317 157 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 156
    simpa using h
  have hprev := st317_p156
  have hstep := st317_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p158 : ((34017538532903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT317 (i+1))
      = (∑ i ∈ Finset.range 157, stT317 (i+1)) + stT317 158 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 157
    simpa using h
  have hprev := st317_p157
  have hstep := st317_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p159 : ((33410876751411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT317 (i+1))
      = (∑ i ∈ Finset.range 158, stT317 (i+1)) + stT317 159 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 158
    simpa using h
  have hprev := st317_p158
  have hstep := st317_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p160 : ((34121221971567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT317 (i+1))
      = (∑ i ∈ Finset.range 159, stT317 (i+1)) + stT317 160 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 159
    simpa using h
  have hprev := st317_p159
  have hstep := st317_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p161 : ((34160454875477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT317 (i+1))
      = (∑ i ∈ Finset.range 160, stT317 (i+1)) + stT317 161 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 160
    simpa using h
  have hprev := st317_p160
  have hstep := st317_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p162 : ((33420246887727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT317 (i+1))
      = (∑ i ∈ Finset.range 161, stT317 (i+1)) + stT317 162 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 161
    simpa using h
  have hprev := st317_p161
  have hstep := st317_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p163 : ((33937906554767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT317 (i+1))
      = (∑ i ∈ Finset.range 162, stT317 (i+1)) + stT317 163 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 162
    simpa using h
  have hprev := st317_p162
  have hstep := st317_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p164 : ((34298833895651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT317 (i+1))
      = (∑ i ∈ Finset.range 163, stT317 (i+1)) + stT317 164 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 163
    simpa using h
  have hprev := st317_p163
  have hstep := st317_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p165 : ((33526268615029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT317 (i+1))
      = (∑ i ∈ Finset.range 164, stT317 (i+1)) + stT317 165 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 164
    simpa using h
  have hprev := st317_p164
  have hstep := st317_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p166 : ((33695765028179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT317 (i+1))
      = (∑ i ∈ Finset.range 165, stT317 (i+1)) + stT317 166 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 165
    simpa using h
  have hprev := st317_p165
  have hstep := st317_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p167 : ((17177006847007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT317 (i+1))
      = (∑ i ∈ Finset.range 166, stT317 (i+1)) + stT317 167 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 166
    simpa using h
  have hprev := st317_p166
  have hstep := st317_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p168 : ((33761703891257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT317 (i+1))
      = (∑ i ∈ Finset.range 167, stT317 (i+1)) + stT317 168 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 167
    simpa using h
  have hprev := st317_p167
  have hstep := st317_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p169 : ((16736317671499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT317 (i+1))
      = (∑ i ∈ Finset.range 168, stT317 (i+1)) + stT317 169 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 168
    simpa using h
  have hprev := st317_p168
  have hstep := st317_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p170 : ((17118352793913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT317 (i+1))
      = (∑ i ∈ Finset.range 169, stT317 (i+1)) + stT317 170 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 169
    simpa using h
  have hprev := st317_p169
  have hstep := st317_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p171 : ((17041336695633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT317 (i+1))
      = (∑ i ∈ Finset.range 170, stT317 (i+1)) + stT317 171 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 170
    simpa using h
  have hprev := st317_p170
  have hstep := st317_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p172 : ((33406377937437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT317 (i+1))
      = (∑ i ∈ Finset.range 171, stT317 (i+1)) + stT317 172 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 171
    simpa using h
  have hprev := st317_p171
  have hstep := st317_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p173 : ((16961488574761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT317 (i+1))
      = (∑ i ∈ Finset.range 172, stT317 (i+1)) + stT317 173 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 172
    simpa using h
  have hprev := st317_p172
  have hstep := st317_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p174 : ((17165137956697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT317 (i+1))
      = (∑ i ∈ Finset.range 173, stT317 (i+1)) + stT317 174 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 173
    simpa using h
  have hprev := st317_p173
  have hstep := st317_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p175 : ((6722599361447/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT317 (i+1))
      = (∑ i ∈ Finset.range 174, stT317 (i+1)) + stT317 175 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 174
    simpa using h
  have hprev := st317_p174
  have hstep := st317_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p176 : ((8387043518643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT317 (i+1))
      = (∑ i ∈ Finset.range 175, stT317 (i+1)) + stT317 176 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 175
    simpa using h
  have hprev := st317_p175
  have hstep := st317_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p177 : ((17146234112523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT317 (i+1))
      = (∑ i ∈ Finset.range 176, stT317 (i+1)) + stT317 177 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 176
    simpa using h
  have hprev := st317_p176
  have hstep := st317_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p178 : ((17016150210561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT317 (i+1))
      = (∑ i ∈ Finset.range 177, stT317 (i+1)) + stT317 178 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 177
    simpa using h
  have hprev := st317_p177
  have hstep := st317_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p179 : ((16699381227991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT317 (i+1))
      = (∑ i ∈ Finset.range 178, stT317 (i+1)) + stT317 179 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 178
    simpa using h
  have hprev := st317_p178
  have hstep := st317_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p180 : ((8477330049003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT317 (i+1))
      = (∑ i ∈ Finset.range 179, stT317 (i+1)) + stT317 180 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 179
    simpa using h
  have hprev := st317_p179
  have hstep := st317_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p181 : ((343475306603/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT317 (i+1))
      = (∑ i ∈ Finset.range 180, stT317 (i+1)) + stT317 181 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 180
    simpa using h
  have hprev := st317_p180
  have hstep := st317_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p182 : ((673631640481/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT317 (i+1))
      = (∑ i ∈ Finset.range 181, stT317 (i+1)) + stT317 182 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 181
    simpa using h
  have hprev := st317_p181
  have hstep := st317_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p183 : ((4183883020653/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT317 (i+1))
      = (∑ i ∈ Finset.range 182, stT317 (i+1)) + stT317 183 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 182
    simpa using h
  have hprev := st317_p182
  have hstep := st317_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p184 : ((34201790886487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT317 (i+1))
      = (∑ i ∈ Finset.range 183, stT317 (i+1)) + stT317 184 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 183
    simpa using h
  have hprev := st317_p183
  have hstep := st317_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p185 : ((34190375938397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT317 (i+1))
      = (∑ i ∈ Finset.range 184, stT317 (i+1)) + stT317 185 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 184
    simpa using h
  have hprev := st317_p184
  have hstep := st317_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p186 : ((33465689470157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT317 (i+1))
      = (∑ i ∈ Finset.range 185, stT317 (i+1)) + stT317 186 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 185
    simpa using h
  have hprev := st317_p185
  have hstep := st317_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p187 : ((33669443787517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT317 (i+1))
      = (∑ i ∈ Finset.range 186, stT317 (i+1)) + stT317 187 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 186
    simpa using h
  have hprev := st317_p186
  have hstep := st317_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p188 : ((34340459063041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT317 (i+1))
      = (∑ i ∈ Finset.range 187, stT317 (i+1)) + stT317 188 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 187
    simpa using h
  have hprev := st317_p187
  have hstep := st317_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p189 : ((1359329105281/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT317 (i+1))
      = (∑ i ∈ Finset.range 188, stT317 (i+1)) + stT317 189 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 188
    simpa using h
  have hprev := st317_p188
  have hstep := st317_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p190 : ((8347678832777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT317 (i+1))
      = (∑ i ∈ Finset.range 189, stT317 (i+1)) + stT317 190 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 189
    simpa using h
  have hprev := st317_p189
  have hstep := st317_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p191 : ((8465371038173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT317 (i+1))
      = (∑ i ∈ Finset.range 190, stT317 (i+1)) + stT317 191 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 190
    simpa using h
  have hprev := st317_p190
  have hstep := st317_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p192 : ((1374711606509/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT317 (i+1))
      = (∑ i ∈ Finset.range 191, stT317 (i+1)) + stT317 192 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 191
    simpa using h
  have hprev := st317_p191
  have hstep := st317_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p193 : ((33817993262293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT317 (i+1))
      = (∑ i ∈ Finset.range 192, stT317 (i+1)) + stT317 193 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 192
    simpa using h
  have hprev := st317_p192
  have hstep := st317_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p194 : ((33392444603813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT317 (i+1))
      = (∑ i ∈ Finset.range 193, stT317 (i+1)) + stT317 194 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 193
    simpa using h
  have hprev := st317_p193
  have hstep := st317_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p195 : ((33993221282973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT317 (i+1))
      = (∑ i ∈ Finset.range 194, stT317 (i+1)) + stT317 195 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 194
    simpa using h
  have hprev := st317_p194
  have hstep := st317_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p196 : ((34350905211003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT317 (i+1))
      = (∑ i ∈ Finset.range 195, stT317 (i+1)) + stT317 196 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 195
    simpa using h
  have hprev := st317_p195
  have hstep := st317_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p197 : ((33719581808019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT317 (i+1))
      = (∑ i ∈ Finset.range 196, stT317 (i+1)) + stT317 197 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 196
    simpa using h
  have hprev := st317_p196
  have hstep := st317_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p198 : ((33411756518859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT317 (i+1))
      = (∑ i ∈ Finset.range 197, stT317 (i+1)) + stT317 198 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 197
    simpa using h
  have hprev := st317_p197
  have hstep := st317_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p199 : ((34058468655159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT317 (i+1))
      = (∑ i ∈ Finset.range 198, stT317 (i+1)) + stT317 199 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 198
    simpa using h
  have hprev := st317_p198
  have hstep := st317_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p200 : ((34336048772307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT317 (i+1))
      = (∑ i ∈ Finset.range 199, stT317 (i+1)) + stT317 200 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 199
    simpa using h
  have hprev := st317_p199
  have hstep := st317_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p201 : ((33684471297887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT317 (i+1))
      = (∑ i ∈ Finset.range 200, stT317 (i+1)) + stT317 201 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 200
    simpa using h
  have hprev := st317_p200
  have hstep := st317_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p202 : ((33416337136067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT317 (i+1))
      = (∑ i ∈ Finset.range 201, stT317 (i+1)) + stT317 202 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 201
    simpa using h
  have hprev := st317_p201
  have hstep := st317_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p203 : ((34063752893279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT317 (i+1))
      = (∑ i ∈ Finset.range 202, stT317 (i+1)) + stT317 203 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 202
    simpa using h
  have hprev := st317_p202
  have hstep := st317_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p204 : ((34342302892139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT317 (i+1))
      = (∑ i ∈ Finset.range 203, stT317 (i+1)) + stT317 204 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 203
    simpa using h
  have hprev := st317_p203
  have hstep := st317_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p205 : ((33707367651211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT317 (i+1))
      = (∑ i ∈ Finset.range 204, stT317 (i+1)) + stT317 205 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 204
    simpa using h
  have hprev := st317_p204
  have hstep := st317_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p206 : ((33399134619813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT317 (i+1))
      = (∑ i ∈ Finset.range 205, stT317 (i+1)) + stT317 206 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 205
    simpa using h
  have hprev := st317_p205
  have hstep := st317_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p207 : ((6802212921937/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT317 (i+1))
      = (∑ i ∈ Finset.range 206, stT317 (i+1)) + stT317 207 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 206
    simpa using h
  have hprev := st317_p206
  have hstep := st317_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p208 : ((3436565589131/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT317 (i+1))
      = (∑ i ∈ Finset.range 207, stT317 (i+1)) + stT317 208 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 207
    simpa using h
  have hprev := st317_p207
  have hstep := st317_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p209 : ((675795731053/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT317 (i+1))
      = (∑ i ∈ Finset.range 208, stT317 (i+1)) + stT317 209 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 208
    simpa using h
  have hprev := st317_p208
  have hstep := st317_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p210 : ((3337485676751/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT317 (i+1))
      = (∑ i ∈ Finset.range 209, stT317 (i+1)) + stT317 210 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 209
    simpa using h
  have hprev := st317_p209
  have hstep := st317_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p211 : ((16948467545437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT317 (i+1))
      = (∑ i ∈ Finset.range 210, stT317 (i+1)) + stT317 211 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 210
    simpa using h
  have hprev := st317_p210
  have hstep := st317_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p212 : ((17190387368719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT317 (i+1))
      = (∑ i ∈ Finset.range 211, stT317 (i+1)) + stT317 212 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 211
    simpa using h
  have hprev := st317_p211
  have hstep := st317_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p213 : ((4241763702623/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT317 (i+1))
      = (∑ i ∈ Finset.range 212, stT317 (i+1)) + stT317 213 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 212
    simpa using h
  have hprev := st317_p212
  have hstep := st317_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p214 : ((16689626559287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT317 (i+1))
      = (∑ i ∈ Finset.range 213, stT317 (i+1)) + stT317 214 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 213
    simpa using h
  have hprev := st317_p213
  have hstep := st317_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p215 : ((8431135135707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT317 (i+1))
      = (∑ i ∈ Finset.range 214, stT317 (i+1)) + stT317 215 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 214
    simpa using h
  have hprev := st317_p214
  have hstep := st317_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p216 : ((34342602536747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT317 (i+1))
      = (∑ i ∈ Finset.range 215, stT317 (i+1)) + stT317 216 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 215
    simpa using h
  have hprev := st317_p215
  have hstep := st317_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p217 : ((17063015647621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT317 (i+1))
      = (∑ i ∈ Finset.range 216, stT317 (i+1)) + stT317 217 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 216
    simpa using h
  have hprev := st317_p216
  have hstep := st317_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p218 : ((8365934255213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT317 (i+1))
      = (∑ i ∈ Finset.range 217, stT317 (i+1)) + stT317 218 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 217
    simpa using h
  have hprev := st317_p217
  have hstep := st317_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p219 : ((33525273010757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT317 (i+1))
      = (∑ i ∈ Finset.range 218, stT317 (i+1)) + stT317 219 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 218
    simpa using h
  have hprev := st317_p218
  have hstep := st317_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p220 : ((34198983890681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT317 (i+1))
      = (∑ i ∈ Finset.range 219, stT317 (i+1)) + stT317 220 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 219
    simpa using h
  have hprev := st317_p219
  have hstep := st317_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p221 : ((34311696138329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT317 (i+1))
      = (∑ i ∈ Finset.range 220, stT317 (i+1)) + stT317 221 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 220
    simpa using h
  have hprev := st317_p220
  have hstep := st317_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p222 : ((4209010020193/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT317 (i+1))
      = (∑ i ∈ Finset.range 221, stT317 (i+1)) + stT317 222 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 221
    simpa using h
  have hprev := st317_p221
  have hstep := st317_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p223 : ((8344553073711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT317 (i+1))
      = (∑ i ∈ Finset.range 222, stT317 (i+1)) + stT317 223 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 222
    simpa using h
  have hprev := st317_p222
  have hstep := st317_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p224 : ((16963539969877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT317 (i+1))
      = (∑ i ∈ Finset.range 223, stT317 (i+1)) + stT317 224 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 223
    simpa using h
  have hprev := st317_p223
  have hstep := st317_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p225 : ((8597222702819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT317 (i+1))
      = (∑ i ∈ Finset.range 224, stT317 (i+1)) + stT317 225 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 224
    simpa using h
  have hprev := st317_p224
  have hstep := st317_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p226 : ((33991381317159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT317 (i+1))
      = (∑ i ∈ Finset.range 225, stT317 (i+1)) + stT317 226 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 225
    simpa using h
  have hprev := st317_p225
  have hstep := st317_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p227 : ((33399301013167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT317 (i+1))
      = (∑ i ∈ Finset.range 226, stT317 (i+1)) + stT317 227 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 226
    simpa using h
  have hprev := st317_p226
  have hstep := st317_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p228 : ((33589719707083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT317 (i+1))
      = (∑ i ∈ Finset.range 227, stT317 (i+1)) + stT317 228 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 227
    simpa using h
  have hprev := st317_p227
  have hstep := st317_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p229 : ((34246602535893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT317 (i+1))
      = (∑ i ∈ Finset.range 228, stT317 (i+1)) + stT317 229 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 228
    simpa using h
  have hprev := st317_p228
  have hstep := st317_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p230 : ((34300060450633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT317 (i+1))
      = (∑ i ∈ Finset.range 229, stT317 (i+1)) + stT317 230 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 229
    simpa using h
  have hprev := st317_p229
  have hstep := st317_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p231 : ((6733416993301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT317 (i+1))
      = (∑ i ∈ Finset.range 230, stT317 (i+1)) + stT317 231 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 230
    simpa using h
  have hprev := st317_p230
  have hstep := st317_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p232 : ((16682427297843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT317 (i+1))
      = (∑ i ∈ Finset.range 231, stT317 (i+1)) + stT317 232 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 231
    simpa using h
  have hprev := st317_p231
  have hstep := st317_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p233 : ((6774374347219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT317 (i+1))
      = (∑ i ∈ Finset.range 232, stT317 (i+1)) + stT317 233 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 232
    simpa using h
  have hprev := st317_p232
  have hstep := st317_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p234 : ((1375335756319/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT317 (i+1))
      = (∑ i ∈ Finset.range 233, stT317 (i+1)) + stT317 234 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 233
    simpa using h
  have hprev := st317_p233
  have hstep := st317_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p235 : ((17048908333013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT317 (i+1))
      = (∑ i ∈ Finset.range 234, stT317 (i+1)) + stT317 235 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 234
    simpa using h
  have hprev := st317_p234
  have hstep := st317_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p236 : ((33463696641441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT317 (i+1))
      = (∑ i ∈ Finset.range 235, stT317 (i+1)) + stT317 236 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 235
    simpa using h
  have hprev := st317_p235
  have hstep := st317_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p237 : ((33462250049051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT317 (i+1))
      = (∑ i ∈ Finset.range 236, stT317 (i+1)) + stT317 237 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 236
    simpa using h
  have hprev := st317_p236
  have hstep := st317_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p238 : ((17046043108523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT317 (i+1))
      = (∑ i ∈ Finset.range 237, stT317 (i+1)) + stT317 238 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 237
    simpa using h
  have hprev := st317_p237
  have hstep := st317_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p239 : ((429882885913/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT317 (i+1))
      = (∑ i ∈ Finset.range 238, stT317 (i+1)) + stT317 239 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 238
    simpa using h
  have hprev := st317_p238
  have hstep := st317_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p240 : ((2119267736471/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT317 (i+1))
      = (∑ i ∈ Finset.range 239, stT317 (i+1)) + stT317 240 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 239
    simpa using h
  have hprev := st317_p239
  have hstep := st317_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p241 : ((4171667467243/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT317 (i+1))
      = (∑ i ∈ Finset.range 240, stT317 (i+1)) + stT317 241 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 240
    simpa using h
  have hprev := st317_p240
  have hstep := st317_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p242 : ((1049479155703/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT317 (i+1))
      = (∑ i ∈ Finset.range 241, stT317 (i+1)) + stT317 242 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 241
    simpa using h
  have hprev := st317_p241
  have hstep := st317_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p243 : ((8555807147749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT317 (i+1))
      = (∑ i ∈ Finset.range 242, stT317 (i+1)) + stT317 243 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 242
    simpa using h
  have hprev := st317_p242
  have hstep := st317_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p244 : ((8587530505593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT317 (i+1))
      = (∑ i ∈ Finset.range 243, stT317 (i+1)) + stT317 244 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 243
    simpa using h
  have hprev := st317_p243
  have hstep := st317_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p245 : ((675631886487/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT317 (i+1))
      = (∑ i ∈ Finset.range 244, stT317 (i+1)) + stT317 245 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 244
    simpa using h
  have hprev := st317_p244
  have hstep := st317_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p246 : ((33345320148137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT317 (i+1))
      = (∑ i ∈ Finset.range 245, stT317 (i+1)) + stT317 246 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 245
    simpa using h
  have hprev := st317_p245
  have hstep := st317_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p247 : ((33668313813637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT317 (i+1))
      = (∑ i ∈ Finset.range 246, stT317 (i+1)) + stT317 247 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 246
    simpa using h
  have hprev := st317_p246
  have hstep := st317_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p248 : ((34284662593637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT317 (i+1))
      = (∑ i ∈ Finset.range 247, stT317 (i+1)) + stT317 248 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 247
    simpa using h
  have hprev := st317_p247
  have hstep := st317_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p249 : ((34317920429157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT317 (i+1))
      = (∑ i ∈ Finset.range 248, stT317 (i+1)) + stT317 249 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 248
    simpa using h
  have hprev := st317_p248
  have hstep := st317_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_p250 : ((1348974494821/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT317 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT317 (i+1))
      = (∑ i ∈ Finset.range 249, stT317 (i+1)) + stT317 250 := by
    have h := Finset.sum_range_succ (fun i => stT317 (i+1)) 249
    simpa using h
  have hprev := st317_p249
  have hstep := st317_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st317_s250 :
    |Real.sin (((317 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((394423/500000 : ℚ) : ℝ))
      - ((172779/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 6971899/10000000) (δ := 8003/500000000) (ψ := 394423/500000) 317 278
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 317`** (evaluated boundary). -/
theorem station_317_sign : hardyG ((((317:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 317 250 (by norm_num) (by norm_num)
    ((394423/500000 : ℚ) : ℝ)
  have hchain := st317_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT317 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((317 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((394423/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st317_c250
  have hsinb := abs_le.mp st317_s250
  have hbdy_lo : ((-138007512247/8039140000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((317 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((394423/500000 : ℚ) : ℝ))) / 2
          - ((((317:ℕ)):ℝ))
            * Real.sin (((317 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((394423/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((317:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((317:ℝ) * Real.log (250:ℝ) - ((394423/500000 : ℚ) : ℝ))) / 2
        - ((317:ℝ)) * Real.sin ((317:ℝ) * Real.log (250:ℝ) - ((394423/500000 : ℚ) : ℝ))
        ≥ ((-1745671/16000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((317:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-1745671/16000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-1745671/16000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-1745671/16000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((317:ℕ)):ℝ))+1) * (((((317:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((682200324597/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1348974494821/400000000000 : ℚ) : ℝ) + ((-138007512247/8039140000000 : ℚ) : ℝ)
      - ((682200324597/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((394423/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((317:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((394423/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((317:ℕ)):ℝ)))).re
      - Real.sin ((394423/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((317:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((317:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((317:ℕ)):ℝ))
      = (((((317:ℕ)):ℝ)) * (Real.log ((((317:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((317:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_317
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
  have hθwin : |(((394423/500000 : ℚ) : ℝ) + ((74:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((317:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((317:ℕ)):ℝ)))
    (φ := ((394423/500000 : ℚ) : ℝ) + ((74:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((394423/500000 : ℚ) : ℝ) + ((74:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((394423/500000 : ℚ)) : ℝ) - Real.pi) + ((74:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((394423/500000 : ℚ)) : ℝ) - Real.pi) 74).1,
    (cos_sin_shift ((((394423/500000 : ℚ)) : ℝ) - Real.pi) 74).2]
  exact cos_sin_flip ((394423/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_317_sign
end AxiomAudit
