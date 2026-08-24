import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 267` (rung-280.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT267 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((267 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))

theorem st267_c1 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((123587/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565427/2500000) (δ := 201/1000000000) (ψ := -904683/1000000) 267 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t1 : ((123577/200000 : ℚ) : ℝ) ≤ stT267 1 := by
  have hc : ((123577/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123577/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((123577/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c2 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-406647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1575367/2500000) (δ := 6693/500000000) (ψ := -904683/1000000) 267 30
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t2 : ((-44931333839/78125000000 : ℚ) : ℝ) ≤ stT267 2 := by
  have hc : ((-25417/31250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44931333839/78125000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-25417/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c3 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((475243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2688889/10000000) (δ := 13439/1000000000) (ψ := -904683/1000000) 267 47
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t3 : ((1371763867943/5000000000000 : ℚ) : ℝ) ≤ stT267 3 := by
  have hc : ((475193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1371763867943/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((475193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c4 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((471819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 843353/10000000) (δ := 6739/500000000) (ψ := -904683/1000000) 267 59
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t4 : ((235897/500000 : ℚ) : ℝ) ≤ stT267 4 := by
  have hc : ((235897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235897/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((235897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c5 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-243619/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3643963/5000000) (δ := 13497/1000000000) (ψ := -904683/1000000) 267 69
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t5 : ((-272388300471/625000000000 : ℚ) : ℝ) ≤ stT267 5 := by
  have hc : ((-487263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272388300471/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-487263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c6 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-210001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113983/2500000) (δ := 3339/250000000) (ψ := -904683/1000000) 267 76
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t6 : ((-857529636633/10000000000000 : ℚ) : ℝ) ≤ stT267 6 := by
  have hc : ((-210051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-857529636633/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-210051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c7 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((126191/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2604219/10000000) (δ := 6753/500000000) (ψ := -904683/1000000) 267 83
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t7 : ((238454905227/1250000000000 : ℚ) : ℝ) ≤ stT267 7 := by
  have hc : ((252357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238454905227/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((252357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c8 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-6241/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7719789/10000000) (δ := 13463/1000000000) (ψ := -904683/1000000) 267 89
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t8 : ((-176530980387/500000000000 : ℚ) : ℝ) ≤ stT267 8 := by
  have hc : ((-99861/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176530980387/500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-99861/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c9 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-6227/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7639453/10000000) (δ := 13527/1000000000) (ψ := -904683/1000000) 267 94
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t9 : ((-166061699879/500000000000 : ℚ) : ℝ) ≤ stT267 9 := by
  have hc : ((-99637/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166061699879/500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-99637/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c10 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((998361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35793/2500000) (δ := 6699/500000000) (ψ := -904683/1000000) 267 98
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t10 : ((3156935914147/10000000000000 : ℚ) : ℝ) ≤ stT267 10 := by
  have hc : ((998311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3156935914147/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((998311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c11 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((19339/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 322267/5000000) (δ := 6767/500000000) (ψ := -904683/1000000) 267 102
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t11 : ((29153127597/100000000000 : ℚ) : ℝ) ≤ stT267 11 := by
  have hc : ((9669/10000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29153127597/100000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((9669/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c12 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-2881/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -410721/1000000) (δ := 13363/1000000000) (ψ := -904683/1000000) 267 106
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t12 : ((-260078313/12500000000 : ℚ) : ℝ) ≤ stT267 12 := by
  have hc : ((-2883/40000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260078313/12500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-2883/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c13 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((9968/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1098701/5000000) (δ := 13519/1000000000) (ψ := -904683/1000000) 267 109
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t13 : ((1769221197/10000000000 : ℚ) : ℝ) ≤ stT267 13 := by
  have hc : ((318951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1769221197/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((318951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c14 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-60747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4540603/10000000) (δ := 6753/500000000) (ψ := -904683/1000000) 267 112
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t14 : ((-324773259147/5000000000000 : ℚ) : ℝ) ≤ stT267 14 := by
  have hc : ((-121519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324773259147/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-121519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c15 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((181987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1734737/5000000) (δ := 13527/1000000000) (ψ := -904683/1000000) 267 115
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t15 : ((117439787689/2500000000000 : ℚ) : ℝ) ≤ stT267 15 := by
  have hc : ((181937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117439787689/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((181937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c16 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((973669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -574967/10000000) (δ := 13549/1000000000) (ψ := -904683/1000000) 267 118
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t16 : ((973619/4000000 : ℚ) : ℝ) ≤ stT267 16 := by
  have hc : ((973619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((973619/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((973619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c17 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-242301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7231937/10000000) (δ := 13433/1000000000) (ψ := -904683/1000000) 267 121
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t17 : ((-1175393486839/5000000000000 : ℚ) : ℝ) ≤ stT267 17 := by
  have hc : ((-484627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1175393486839/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-484627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c18 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((980491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -494631/10000000) (δ := 2697/200000000) (ψ := -904683/1000000) 267 123
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t18 : ((1155460503351/5000000000000 : ℚ) : ℝ) ≤ stT267 18 := by
  have hc : ((980441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1155460503351/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((980441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c19 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-6297/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2089649/5000000) (δ := 3351/250000000) (ψ := -904683/1000000) 267 125
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t19 : ((-57813928679/2500000000000 : ℚ) : ℝ) ≤ stT267 19 := by
  have hc : ((-50401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57813928679/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-50401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c20 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-942443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7001649/10000000) (δ := 1349/100000000) (ψ := -904683/1000000) 267 127
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t20 : ((-526869609381/2500000000000 : ℚ) : ℝ) ≤ stT267 20 := by
  have hc : ((-942493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-526869609381/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-942493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c21 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-992847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3777391/5000000) (δ := 1671/125000000) (ψ := -904683/1000000) 267 130
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t21 : ((-2166678982563/10000000000000 : ℚ) : ℝ) ≤ stT267 21 := by
  have hc : ((-992897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2166678982563/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-992897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c22 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-499833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1557871/2000000) (δ := 6721/500000000) (ψ := -904683/1000000) 267 131
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t22 : ((-66606328429/312500000000 : ℚ) : ℝ) ≤ stT267 22 := by
  have hc : ((-249929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66606328429/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-249929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c23 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-749433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1209001/2000000) (δ := 841/62500000) (ψ := -904683/1000000) 267 133
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t23 : ((-312556146007/2000000000000 : ℚ) : ℝ) ≤ stT267 23 := by
  have hc : ((-749483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312556146007/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-749483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c24 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((69659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3037611/10000000) (δ := 1679/125000000) (ψ := -904683/1000000) 267 135
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t24 : ((142170394409/2000000000000 : ℚ) : ℝ) ≤ stT267 24 := by
  have hc : ((69649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142170394409/2000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((69649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c25 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((22491/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112963/1000000) (δ := 2697/200000000) (ψ := -904683/1000000) 267 137
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t25 : ((89959/500000 : ℚ) : ℝ) ≤ stT267 25 := by
  have hc : ((89959/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89959/500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((89959/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c26 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-413991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -318287/500000) (δ := 211/15625000) (ψ := -904683/1000000) 267 139
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t26 : ((-6343378489/39062500000 : ℚ) : ℝ) ≤ stT267 26 := by
  have hc : ((-12938/15625 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6343378489/39062500000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-12938/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c27 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((158999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3117947/10000000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 140
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t27 : ((305945463/5000000000 : ℚ) : ℝ) ≤ stT267 27 := by
  have hc : ((79487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305945463/5000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((79487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c28 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-3821/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4022539/10000000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 142
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t28 : ((-3615231399/500000000000 : ℚ) : ℝ) ≤ stT267 28 := by
  have hc : ((-1913/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3615231399/500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-1913/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c29 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((23371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184647/500000) (δ := 107/8000000) (ψ := -904683/1000000) 267 143
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t29 : ((86751273301/5000000000000 : ℚ) : ℝ) ≤ stT267 29 := by
  have hc : ((46717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86751273301/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((46717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c30 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-22497/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1018747/2000000) (δ := 13443/1000000000) (ψ := -904683/1000000) 267 145
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t30 : ((-41078282129/500000000000 : ℚ) : ℝ) ≤ stT267 30 := by
  have hc : ((-44999/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41078282129/500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-44999/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c31 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((907197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27139/250000) (δ := 269/20000000) (ψ := -904683/1000000) 267 146
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t31 : ((1629284090791/10000000000000 : ℚ) : ℝ) ≤ stT267 31 := by
  have hc : ((907147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1629284090791/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((907147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c32 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-217739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3284927/5000000) (δ := 13457/1000000000) (ψ := -904683/1000000) 267 147
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t32 : ((-769867831801/5000000000000 : ℚ) : ℝ) ≤ stT267 32 := by
  have hc : ((-435503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-769867831801/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-435503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c33 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-30207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430603/1000000) (δ := 1679/125000000) (ψ := -904683/1000000) 267 149
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t33 : ((-52601058609/2000000000000 : ℚ) : ℝ) ≤ stT267 33 := by
  have hc : ((-30217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52601058609/2000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-30217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c34 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((999393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21779/2500000) (δ := 541/40000000) (ψ := -904683/1000000) 267 150
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t34 : ((342771650971/2000000000000 : ℚ) : ℝ) ≤ stT267 34 := by
  have hc : ((999343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342771650971/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((999343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c35 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((148613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3554077/10000000) (δ := 13517/1000000000) (ψ := -904683/1000000) 267 151
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t35 : ((62779306851/2500000000000 : ℚ) : ℝ) ≤ stT267 35 := by
  have hc : ((148563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62779306851/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((148563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c36 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-443147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665019/1000000) (δ := 13393/1000000000) (ψ := -904683/1000000) 267 152
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t36 : ((-184655036931/1250000000000 : ℚ) : ℝ) ≤ stT267 36 := by
  have hc : ((-110793/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184655036931/1250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-110793/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c37 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-85209/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -809613/1250000) (δ := 13407/1000000000) (ψ := -904683/1000000) 267 154
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t37 : ((-7004548193/50000000000 : ℚ) : ℝ) ≤ stT267 37 := by
  have hc : ((-42607/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7004548193/50000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-42607/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c38 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-90863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1095961/2500000) (δ := 13389/1000000000) (ψ := -904683/1000000) 267 155
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t38 : ((-3685996923/125000000000 : ℚ) : ℝ) ≤ stT267 38 := by
  have hc : ((-11361/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3685996923/125000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-11361/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c39 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((452469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2753161/10000000) (δ := 13381/1000000000) (ψ := -904683/1000000) 267 156
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t39 : ((724449948739/10000000000000 : ℚ) : ℝ) ≤ stT267 39 := by
  have hc : ((452419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((724449948739/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((452419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c40 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((811199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1561493/10000000) (δ := 6737/500000000) (ψ := -904683/1000000) 267 157
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t40 : ((641269253781/5000000000000 : ℚ) : ℝ) ≤ stT267 40 := by
  have hc : ((811149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((641269253781/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((811149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c41 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((23771/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157429/2000000) (δ := 423/31250000) (ψ := -904683/1000000) 267 158
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t41 : ((148488392223/1000000000000 : ℚ) : ℝ) ≤ stT267 41 := by
  have hc : ((95079/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148488392223/1000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((95079/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c42 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((197317/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409961/10000000) (δ := 673/50000000) (ψ := -904683/1000000) 267 159
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t42 : ((304451212131/2000000000000 : ℚ) : ℝ) ≤ stT267 42 := by
  have hc : ((197307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304451212131/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((197307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c43 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((15414/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82263/2000000) (δ := 269/20000000) (ψ := -904683/1000000) 267 160
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t43 : ((150431535331/1000000000000 : ℚ) : ℝ) ≤ stT267 43 := by
  have hc : ((493223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150431535331/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((493223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c44 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((952481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -773787/10000000) (δ := 13457/1000000000) (ψ := -904683/1000000) 267 161
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t44 : ((358960767159/2500000000000 : ℚ) : ℝ) ≤ stT267 44 := by
  have hc : ((952431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358960767159/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((952431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c45 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((12962/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481157/10000000) (δ := 6769/500000000) (ψ := -904683/1000000) 267 162
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t45 : ((618285803649/5000000000000 : ℚ) : ℝ) ≤ stT267 45 := by
  have hc : ((414759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((618285803649/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((414759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c46 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((534161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -629551/2500000) (δ := 3343/250000000) (ψ := -904683/1000000) 267 163
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t46 : ((787503406509/10000000000000 : ℚ) : ℝ) ≤ stT267 46 := by
  have hc : ((534111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((787503406509/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((534111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c47 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((2251/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -483839/1250000) (δ := 13379/1000000000) (ψ := -904683/1000000) 267 164
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t47 : ((1638062827/500000000000 : ℚ) : ℝ) ≤ stT267 47 := by
  have hc : ((1123/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1638062827/500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((1123/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c48 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-596727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5525531/10000000) (δ := 13417/1000000000) (ψ := -904683/1000000) 267 165
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t48 : ((-53835849947/625000000000 : ℚ) : ℝ) ≤ stT267 48 := by
  have hc : ((-596777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53835849947/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-596777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c49 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-988239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3735089/5000000) (δ := 13393/1000000000) (ψ := -904683/1000000) 267 166
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t49 : ((-352960498327/2500000000000 : ℚ) : ℝ) ≤ stT267 49 := by
  have hc : ((-988289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352960498327/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-988289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c50 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-185371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6015191/10000000) (δ := 13393/1000000000) (ψ := -904683/1000000) 267 166
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t50 : ((-262171941069/2500000000000 : ℚ) : ℝ) ≤ stT267 50 := by
  have hc : ((-370767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262171941069/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-370767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c51 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((159921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3525463/10000000) (δ := 13403/1000000000) (ψ := -904683/1000000) 267 167
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t51 : ((5596604097/250000000000 : ℚ) : ℝ) ≤ stT267 51 := by
  have hc : ((159871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5596604097/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((159871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c52 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((475917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 389541/5000000) (δ := 3377/250000000) (ψ := -904683/1000000) 267 168
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t52 : ((659943231/5000000000 : ℚ) : ℝ) ≤ stT267 52 := by
  have hc : ((118973/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((659943231/5000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((118973/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c53 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((632761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34597/156250) (δ := 2683/200000000) (ψ := -904683/1000000) 267 169
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t53 : ((173818998631/2000000000000 : ℚ) : ℝ) ≤ stT267 53 := by
  have hc : ((632711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173818998631/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((632711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c54 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-570637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1089039/2000000) (δ := 13481/1000000000) (ψ := -904683/1000000) 267 170
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t54 : ((-194151712209/2500000000000 : ℚ) : ℝ) ≤ stT267 54 := by
  have hc : ((-570687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194151712209/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-570687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c55 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-912901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680283/1000000) (δ := 6761/500000000) (ψ := -904683/1000000) 267 170
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t55 : ((-3077557821/25000000000 : ℚ) : ℝ) ≤ stT267 55 := by
  have hc : ((-912951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3077557821/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-912951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c56 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((316379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 624443/2000000) (δ := 6687/500000000) (ψ := -904683/1000000) 267 171
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t56 : ((211356170337/5000000000000 : ℚ) : ℝ) ≤ stT267 56 := by
  have hc : ((316329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211356170337/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((316329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c57 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((238197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154253/2000000) (δ := 3359/250000000) (ψ := -904683/1000000) 267 172
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t57 : ((157741496077/1250000000000 : ℚ) : ℝ) ≤ stT267 57 := by
  have hc : ((476369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157741496077/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((476369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c58 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-368397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2435101/5000000) (δ := 13359/1000000000) (ψ := -904683/1000000) 267 173
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t58 : ((-96758972011/2000000000000 : ℚ) : ℝ) ≤ stT267 58 := by
  have hc : ((-368447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96758972011/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-368447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c59 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-865089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 654031/1000000) (δ := 13359/1000000000) (ψ := -904683/1000000) 267 173
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t59 : ((-112631581271/1000000000000 : ℚ) : ℝ) ≤ stT267 59 := by
  have hc : ((-865139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112631581271/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-865139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c60 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((42619/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1025543/5000000) (δ := 1669/125000000) (ψ := -904683/1000000) 267 174
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t60 : ((220067355719/2500000000000 : ℚ) : ℝ) ≤ stT267 60 := by
  have hc : ((340927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220067355719/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((340927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c61 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((498067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262357/1000000) (δ := 2709/200000000) (ψ := -904683/1000000) 267 175
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t61 : ((39852814391/625000000000 : ℚ) : ℝ) ≤ stT267 61 := by
  have hc : ((498017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39852814391/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((498017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c62 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-988691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7477649/10000000) (δ := 2673/200000000) (ψ := -904683/1000000) 267 176
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t62 : ((-627851523741/5000000000000 : ℚ) : ℝ) ≤ stT267 62 := by
  have hc : ((-988741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-627851523741/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-988741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c63 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((17857/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1601309/5000000) (δ := 2673/200000000) (ψ := -904683/1000000) 267 176
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t63 : ((179950063111/5000000000000 : ℚ) : ℝ) ≤ stT267 63 := by
  have hc : ((142831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179950063111/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((142831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c64 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((698611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -398671/2000000) (δ := 3343/250000000) (ψ := -904683/1000000) 267 177
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t64 : ((698561/8000000 : ℚ) : ℝ) ≤ stT267 64 := by
  have hc : ((698561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((698561/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((698561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c65 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-97993/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1470453/2000000) (δ := 839/62500000) (ψ := -904683/1000000) 267 178
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t65 : ((-15193952913/125000000000 : ℚ) : ℝ) ≤ stT267 65 := by
  have hc : ((-48999/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15193952913/125000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-48999/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c66 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((13177/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2838791/10000000) (δ := 3381/250000000) (ψ := -904683/1000000) 267 178
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t66 : ((129742643799/2500000000000 : ℚ) : ℝ) ≤ stT267 66 := by
  have hc : ((210807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129742643799/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((210807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c67 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((424353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1415687/5000000) (δ := 3379/250000000) (ψ := -904683/1000000) 267 179
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t67 : ((259184214641/5000000000000 : ℚ) : ℝ) ≤ stT267 67 := by
  have hc : ((424303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259184214641/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((424303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c68 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-949703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3528853/5000000) (δ := 13487/1000000000) (ψ := -904683/1000000) 267 179
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t68 : ((-1151745518287/10000000000000 : ℚ) : ℝ) ≤ stT267 68 := by
  have hc : ((-949753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1151745518287/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-949753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c69 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((905697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1094441/10000000) (δ := 13509/1000000000) (ψ := -904683/1000000) 267 180
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t69 : ((545135193063/5000000000000 : ℚ) : ℝ) ≤ stT267 69 := by
  have hc : ((905647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((545135193063/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((905647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c70 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-419441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1001813/2000000) (δ := 6751/500000000) (ψ := -904683/1000000) 267 181
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t70 : ((-501387808439/10000000000000 : ℚ) : ℝ) ≤ stT267 70 := by
  have hc : ((-419491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501387808439/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-419491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c71 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-105631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1114789/2500000) (δ := 13401/1000000000) (ψ := -904683/1000000) 267 181
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t71 : ((-7836914937/312500000000 : ℚ) : ℝ) ≤ stT267 71 := by
  have hc : ((-13207/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7836914937/312500000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-13207/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c72 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((721257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239119/1250000) (δ := 419/31250000) (ψ := -904683/1000000) 267 182
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t72 : ((849950382777/10000000000000 : ℚ) : ℝ) ≤ stT267 72 := by
  have hc : ((721207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((849950382777/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((721207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c73 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-39001/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1823519/2500000) (δ := 3377/250000000) (ψ := -904683/1000000) 267 182
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t73 : ((-11412394809/100000000000 : ℚ) : ℝ) ≤ stT267 73 := by
  have hc : ((-39003/40000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11412394809/100000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-39003/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c74 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((96453/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13357/200000) (δ := 843/62500000) (ψ := -904683/1000000) 267 183
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t74 : ((437962833/3906250000 : ℚ) : ℝ) ≤ stT267 74 := by
  have hc : ((3014/3125 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437962833/3906250000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((3014/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c75 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-379339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3040097/5000000) (δ := 337/25000000) (ψ := -904683/1000000) 267 184
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t75 : ((-109512997541/1250000000000 : ℚ) : ℝ) ≤ stT267 75 := by
  have hc : ((-94841/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109512997541/1250000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-94841/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c76 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((449679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2760977/10000000) (δ := 337/25000000) (ψ := -904683/1000000) 267 184
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t76 : ((257879767031/5000000000000 : ℚ) : ℝ) ≤ stT267 76 := by
  have hc : ((449629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257879767031/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((449629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c77 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-4699/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4221359/10000000) (δ := 1343/100000000) (ψ := -904683/1000000) 267 185
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t77 : ((-2678643903/200000000000 : ℚ) : ℝ) ≤ stT267 77 := by
  have hc : ((-4701/40000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2678643903/200000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-4701/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c78 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-184799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 219583/500000) (δ := 13473/1000000000) (ψ := -904683/1000000) 267 185
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t78 : ((-104650228011/5000000000000 : ℚ) : ℝ) ≤ stT267 78 := by
  have hc : ((-184849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104650228011/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-184849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c79 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((430989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140651/500000) (δ := 13537/1000000000) (ψ := -904683/1000000) 267 186
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t79 : ((484843866693/10000000000000 : ℚ) : ℝ) ≤ stT267 79 := by
  have hc : ((430939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484843866693/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((430939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c80 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-307559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5583329/10000000) (δ := 13537/1000000000) (ψ := -904683/1000000) 267 186
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t80 : ((-1343317851/19531250000 : ℚ) : ℝ) ≤ stT267 80 := by
  have hc : ((-9612/15625 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1343317851/19531250000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-9612/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c81 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((743139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -229077/1250000) (δ := 13359/1000000000) (ψ := -904683/1000000) 267 187
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t81 : ((825654361879/10000000000000 : ℚ) : ℝ) ≤ stT267 81 := by
  have hc : ((743089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((825654361879/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((743089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c82 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-826169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1589419/2500000) (δ := 3361/250000000) (ψ := -904683/1000000) 267 187
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t82 : ((-228101715301/2500000000000 : ℚ) : ℝ) ≤ stT267 82 := by
  have hc : ((-826219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228101715301/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-826219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c83 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((437901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1259253/10000000) (δ := 1669/125000000) (ψ := -904683/1000000) 267 188
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t83 : ((60078886049/625000000000 : ℚ) : ℝ) ≤ stT267 83 := by
  have hc : ((109469/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60078886049/625000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((109469/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c84 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-450731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6734827/10000000) (δ := 209/7812500) (ψ := -904683/1000000) 267 188
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t84 : ((-12295384101/125000000000 : ℚ) : ℝ) ≤ stT267 84 := by
  have hc : ((-112689/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12295384101/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-112689/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c85 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((113649/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1073641/10000000) (δ := 2689/200000000) (ψ := -904683/1000000) 267 189
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t85 : ((123262836073/1250000000000 : ℚ) : ℝ) ≤ stT267 85 := by
  have hc : ((454571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123262836073/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((454571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c86 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-901221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6733439/10000000) (δ := 2689/200000000) (ψ := -904683/1000000) 267 189
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t86 : ((-121483219361/1250000000000 : ℚ) : ℝ) ≤ stT267 86 := by
  have hc : ((-901271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121483219361/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-901271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c87 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((876117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257623/10000000) (δ := 6733/500000000) (ψ := -904683/1000000) 267 190
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t87 : ((58702621469/625000000000 : ℚ) : ℝ) ≤ stT267 87 := by
  have hc : ((876067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58702621469/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((876067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c88 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-51823/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3185517/5000000) (δ := 6683/500000000) (ψ := -904683/1000000) 267 190
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t88 : ((-110493713109/1250000000000 : ℚ) : ℝ) ≤ stT267 88 := by
  have hc : ((-414609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110493713109/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-414609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c89 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((753251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1794513/10000000) (δ := 13373/1000000000) (ψ := -904683/1000000) 267 191
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t89 : ((798390800397/10000000000000 : ℚ) : ℝ) ≤ stT267 89 := by
  have hc : ((753201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((798390800397/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((753201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c90 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-160033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1132733/2000000) (δ := 13473/1000000000) (ψ := -904683/1000000) 267 191
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t90 : ((-337405682463/5000000000000 : ℚ) : ℝ) ≤ stT267 90 := by
  have hc : ((-320091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337405682463/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-320091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c91 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((96479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -667131/2500000) (δ := 26823/1000000000) (ψ := -904683/1000000) 267 192
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t91 : ((25281727299/500000000000 : ℚ) : ℝ) ≤ stT267 91 := by
  have hc : ((96469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25281727299/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((96469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c92 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-69053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4626617/10000000) (δ := 13423/1000000000) (ψ := -904683/1000000) 267 192
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t92 : ((-144011651063/5000000000000 : ℚ) : ℝ) ≤ stT267 92 := by
  have hc : ((-138131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144011651063/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-138131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c93 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((12383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -386507/1000000) (δ := 13487/1000000000) (ψ := -904683/1000000) 267 193
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t93 : ((6407320229/2500000000000 : ℚ) : ℝ) ≤ stT267 93 := by
  have hc : ((6179/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6407320229/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((6179/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c94 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((12911/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1637021/5000000) (δ := 3379/250000000) (ψ := -904683/1000000) 267 193
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t94 : ((26628195957/1000000000000 : ℚ) : ℝ) ≤ stT267 94 := by
  have hc : ((25817/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26628195957/1000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((25817/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c95 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-272903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5370369/10000000) (δ := 6697/500000000) (ψ := -904683/1000000) 267 194
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t95 : ((-8750574891/156250000000 : ℚ) : ℝ) ≤ stT267 95 := by
  have hc : ((-8529/15625 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8750574891/156250000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-8529/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c96 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((19937/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202403/1250000) (δ := 6747/500000000) (ψ := -904683/1000000) 267 194
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t96 : ((4069365033/50000000000 : ℚ) : ℝ) ≤ stT267 96 := by
  have hc : ((79743/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4069365033/50000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((79743/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c97 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-30093/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7171571/10000000) (δ := 13501/1000000000) (ψ := -904683/1000000) 267 195
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t97 : ((-488902780011/5000000000000 : ℚ) : ℝ) ≤ stT267 97 := by
  have hc : ((-481513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-488902780011/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-481513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c98 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((991543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325357/10000000) (δ := 13401/1000000000) (ψ := -904683/1000000) 267 195
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t98 : ((125194829617/1250000000000 : ℚ) : ℝ) ≤ stT267 98 := by
  have hc : ((991493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125194829617/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((991493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c99 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-8467/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645137/1000000) (δ := 13401/1000000000) (ψ := -904683/1000000) 267 195
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t99 : ((-1702031853/20000000000 : ℚ) : ℝ) ≤ stT267 99 := by
  have hc : ((-3387/4000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1702031853/20000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-3387/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c100 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((524041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1274009/5000000) (δ := 6697/500000000) (ψ := -904683/1000000) 267 196
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t100 : ((523990476009/10000000000000 : ℚ) : ℝ) ≤ stT267 100 := by
  have hc : ((523991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((523990476009/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((523991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c101 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-4169/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2046937/5000000) (δ := 6697/500000000) (ψ := -904683/1000000) 267 196
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t101 : ((-16605691663/2500000000000 : ℚ) : ℝ) ≤ stT267 101 := by
  have hc : ((-33377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16605691663/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-33377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c102 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-107451/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5037679/10000000) (δ := 13387/1000000000) (ψ := -904683/1000000) 267 197
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t102 : ((-53202384799/1250000000000 : ℚ) : ℝ) ≤ stT267 102 := by
  have hc : ((-214927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53202384799/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-214927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c103 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((103881/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 737259/5000000) (δ := 1677/125000000) (ψ := -904683/1000000) 267 197
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t103 : ((409403214171/5000000000000 : ℚ) : ℝ) ≤ stT267 103 := by
  have hc : ((415499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409403214171/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((415499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c104 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-99961/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7784127/10000000) (δ := 13423/1000000000) (ψ := -904683/1000000) 267 198
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t104 : ((-49012380123/500000000000 : ℚ) : ℝ) ≤ stT267 104 := by
  have hc : ((-49983/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49012380123/500000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-49983/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c105 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((848001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -698243/5000000) (δ := 669/50000000) (ψ := -904683/1000000) 267 198
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t105 : ((8275153809/100000000000 : ℚ) : ℝ) ≤ stT267 105 := by
  have hc : ((847951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8275153809/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((847951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c106 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-48841/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2465273/5000000) (δ := 337/25000000) (ψ := -904683/1000000) 267 198
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t106 : ((-94889300127/2500000000000 : ℚ) : ℝ) ≤ stT267 106 := by
  have hc : ((-195389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94889300127/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-195389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c107 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-230989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180389/400000) (δ := 1353/100000000) (ψ := -904683/1000000) 267 199
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t107 : ((-223353949743/10000000000000 : ℚ) : ℝ) ≤ stT267 107 := by
  have hc : ((-231039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223353949743/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-231039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c108 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((777667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1699627/10000000) (δ := 1353/100000000) (ψ := -904683/1000000) 267 199
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t108 : ((2993047833/40000000000 : ℚ) : ℝ) ≤ stT267 108 := by
  have hc : ((777617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2993047833/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((777617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c109 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7851707/10000000) (δ := 13373/1000000000) (ψ := -904683/1000000) 267 199
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t109 : ((-19157497827/200000000000 : ℚ) : ℝ) ≤ stT267 109 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19157497827/200000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c110 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((381089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220039/1250000) (δ := 13537/1000000000) (ψ := -904683/1000000) 267 200
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t110 : ((22708127723/312500000000 : ℚ) : ℝ) ≤ stT267 110 := by
  have hc : ((47633/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22708127723/312500000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((47633/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c111 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-140931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267531/625000) (δ := 13437/1000000000) (ψ := -904683/1000000) 267 200
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t111 : ((-66906621999/5000000000000 : ℚ) : ℝ) ≤ stT267 111 := by
  have hc : ((-140981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66906621999/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-140981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c112 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-284617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5440927/10000000) (δ := 6679/500000000) (ψ := -904683/1000000) 267 201
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t112 : ((-8405051297/156250000000 : ℚ) : ℝ) ≤ stT267 112 := by
  have hc : ((-142321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8405051297/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-142321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c113 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((49033/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 492481/10000000) (δ := 2709/200000000) (ψ := -904683/1000000) 267 201
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t113 : ((1153099299/12500000000 : ℚ) : ℝ) ≤ stT267 113 := by
  have hc : ((98061/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1153099299/12500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((98061/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c114 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-829731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1593389/2500000) (δ := 6679/500000000) (ψ := -904683/1000000) 267 201
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t114 : ((-388580633833/5000000000000 : ℚ) : ℝ) ≤ stT267 114 := by
  have hc : ((-829781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388580633833/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-829781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c115 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((168129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3504663/10000000) (δ := 13551/1000000000) (ψ := -904683/1000000) 267 202
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t115 : ((19591792477/1250000000000 : ℚ) : ℝ) ≤ stT267 115 := by
  have hc : ((168079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19591792477/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((168079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c116 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((613887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284319/1250000) (δ := 13551/1000000000) (ψ := -904683/1000000) 267 202
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t116 : ((142483230603/2500000000000 : ℚ) : ℝ) ≤ stT267 116 := by
  have hc : ((613837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142483230603/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((613837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c117 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-499097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1925931/2500000) (δ := 13459/1000000000) (ψ := -904683/1000000) 267 203
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t117 : ((-230719394061/2500000000000 : ℚ) : ℝ) ≤ stT267 117 := by
  have hc : ((-249561/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230719394061/2500000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-249561/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c118 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((345063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126427/625000) (δ := 13359/1000000000) (ψ := -904683/1000000) 267 203
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t118 : ((79408252953/1250000000000 : ℚ) : ℝ) ≤ stT267 118 := by
  have hc : ((172519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79408252953/1250000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((172519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c119 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((12643/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3610067/10000000) (δ := 13359/1000000000) (ψ := -904683/1000000) 267 203
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t119 : ((2896307331/250000000000 : ℚ) : ℝ) ≤ stT267 119 := by
  have hc : ((6319/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2896307331/250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((6319/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c120 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-171873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -814007/1250000) (δ := 6683/500000000) (ψ := -904683/1000000) 267 204
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t120 : ((-156907006093/2000000000000 : ℚ) : ℝ) ≤ stT267 120 := by
  have hc : ((-171883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156907006093/2000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-171883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c121 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((925273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -972607/10000000) (δ := 6683/500000000) (ψ := -904683/1000000) 267 204
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t121 : ((84111097707/1000000000000 : ℚ) : ℝ) ≤ stT267 121 := by
  have hc : ((925223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84111097707/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((925223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c122 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-14717/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1130313/2500000) (δ := 6733/500000000) (ψ := -904683/1000000) 267 204
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t122 : ((-53307931719/2500000000000 : ℚ) : ℝ) ≤ stT267 122 := by
  have hc : ((-117761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53307931719/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-117761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c123 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-331301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5737709/10000000) (δ := 1343/100000000) (ψ := -904683/1000000) 267 205
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t123 : ((-14937335721/250000000000 : ℚ) : ℝ) ≤ stT267 123 := by
  have hc : ((-165663/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14937335721/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-165663/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c124 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((991151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83207/2500000) (δ := 1343/100000000) (ψ := -904683/1000000) 267 205
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t124 : ((445017233313/5000000000000 : ℚ) : ℝ) ≤ stT267 124 := by
  have hc : ((991101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445017233313/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((991101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c125 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-213273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2514333/5000000) (δ := 13473/1000000000) (ψ := -904683/1000000) 267 205
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t125 : ((-23847462943/625000000000 : ℚ) : ℝ) ≤ stT267 125 := by
  have hc : ((-106649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23847462943/625000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-106649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c126 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-542503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1340131/2500000) (δ := 669/50000000) (ψ := -904683/1000000) 267 206
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t126 : ((-483344733663/10000000000000 : ℚ) : ℝ) ≤ stT267 126 := by
  have hc : ((-542553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483344733663/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-542553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c127 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((999437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8387/1000000) (δ := 13423/1000000000) (ψ := -904683/1000000) 267 206
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t127 : ((221703012693/2500000000000 : ℚ) : ℝ) ≤ stT267 127 := by
  have hc : ((999387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221703012693/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((999387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c128 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-470441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2575733/5000000) (δ := 13423/1000000000) (ψ := -904683/1000000) 267 206
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t128 : ((-103964866761/2500000000000 : ℚ) : ℝ) ≤ stT267 128 := by
  have hc : ((-470491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103964866761/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-470491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c129 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-271479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5361879/10000000) (δ := 2703/200000000) (ψ := -904683/1000000) 267 207
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t129 : ((-14940373019/312500000000 : ℚ) : ℝ) ≤ stT267 129 := by
  have hc : ((-16969/31250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14940373019/312500000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-16969/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c130 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((996559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51861/2500000) (δ := 2703/200000000) (ψ := -904683/1000000) 267 207
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t130 : ((436998095261/5000000000000 : ℚ) : ℝ) ≤ stT267 130 := by
  have hc : ((996509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436998095261/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((996509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c131 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-382241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2453771/5000000) (δ := 2683/200000000) (ψ := -904683/1000000) 267 207
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t131 : ((-66801911631/2000000000000 : ℚ) : ℝ) ≤ stT267 131 := by
  have hc : ((-382291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66801911631/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-382291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c132 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-65859/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5724351/10000000) (δ := 3377/250000000) (ψ := -904683/1000000) 267 208
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t132 : ((-7165912637/125000000000 : ℚ) : ℝ) ≤ stT267 132 := by
  have hc : ((-8233/12500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7165912637/125000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-8233/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c133 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((962523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137319/2000000) (δ := 3377/250000000) (ψ := -904683/1000000) 267 208
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t133 : ((834569000557/10000000000000 : ℚ) : ℝ) ≤ stT267 133 := by
  have hc : ((962473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((834569000557/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((962473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c134 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-30791/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2156707/5000000) (δ := 3351/125000000) (ψ := -904683/1000000) 267 208
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t134 : ((-26608029069/2000000000000 : ℚ) : ℝ) ≤ stT267 134 := by
  have hc : ((-30801/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26608029069/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-30801/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c135 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-210623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160793/250000) (δ := 13401/1000000000) (ψ := -904683/1000000) 267 209
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t135 : ((-362572362673/5000000000000 : ℚ) : ℝ) ≤ stT267 135 := by
  have hc : ((-421271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362572362673/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-421271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c136 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((824091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1505503/10000000) (δ := 6701/500000000) (ψ := -904683/1000000) 267 209
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t136 : ((176652141293/2500000000000 : ℚ) : ℝ) ≤ stT267 136 := by
  have hc : ((824041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176652141293/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((824041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c137 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((215231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3384669/10000000) (δ := 6751/500000000) (ψ := -904683/1000000) 267 209
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t137 : ((183841393617/10000000000000 : ℚ) : ℝ) ≤ stT267 137 := by
  have hc : ((215181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183841393617/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((215181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c138 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-123519/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7468767/10000000) (δ := 13509/1000000000) (ψ := -904683/1000000) 267 210
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t138 : ((-420606934957/5000000000000 : ℚ) : ℝ) ≤ stT267 138 := by
  have hc : ((-494101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-420606934957/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-494101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c139 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((97829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2649217/10000000) (δ := 13409/1000000000) (ψ := -904683/1000000) 267 210
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t139 : ((20742225493/500000000000 : ℚ) : ℝ) ≤ stT267 139 := by
  have hc : ((97819/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20742225493/500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((97819/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c140 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((82093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2135757/10000000) (δ := 13509/1000000000) (ψ := -904683/1000000) 267 210
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t140 : ((138751890219/2500000000000 : ℚ) : ℝ) ≤ stT267 140 := by
  have hc : ((328347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138751890219/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((328347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c141 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-926067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6886621/10000000) (δ := 6697/500000000) (ψ := -904683/1000000) 267 210
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t141 : ((-97491410473/1250000000000 : ℚ) : ℝ) ≤ stT267 141 := by
  have hc : ((-926117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97491410473/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-926117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c142 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-70739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2051993/5000000) (δ := 1677/125000000) (ψ := -904683/1000000) 267 211
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t142 : ((-29702427299/5000000000000 : ℚ) : ℝ) ≤ stT267 142 := by
  have hc : ((-70789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29702427299/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-70789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c143 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((15206/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290131/5000000) (δ := 1677/125000000) (ψ := -904683/1000000) 267 211
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t143 : ((203443880607/2500000000000 : ℚ) : ℝ) ≤ stT267 143 := by
  have hc : ((486567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203443880607/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((486567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c144 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-498549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2615901/5000000) (δ := 13487/1000000000) (ψ := -904683/1000000) 267 211
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t144 : ((-207749749533/5000000000000 : ℚ) : ℝ) ≤ stT267 144 := by
  have hc : ((-498599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207749749533/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-498599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c145 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-348747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5856727/10000000) (δ := 839/62500000) (ψ := -904683/1000000) 267 212
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t145 : ((-14481972563/250000000000 : ℚ) : ℝ) ≤ stT267 145 := by
  have hc : ((-87193/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14481972563/250000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-87193/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c146 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((873901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -634533/5000000) (δ := 3381/250000000) (ψ := -904683/1000000) 267 212
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t146 : ((144640691371/2000000000000 : ℚ) : ℝ) ≤ stT267 146 := by
  have hc : ((873851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144640691371/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((873851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c147 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((253123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1643611/5000000) (δ := 839/62500000) (ψ := -904683/1000000) 267 212
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t147 : ((104365533689/5000000000000 : ℚ) : ℝ) ≤ stT267 147 := by
  have hc : ((253073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104365533689/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((253073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c148 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-999863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122073/156250) (δ := 3381/250000000) (ψ := -904683/1000000) 267 212
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t148 : ((-164384697287/2000000000000 : ℚ) : ℝ) ≤ stT267 148 := by
  have hc : ((-999913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164384697287/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-999913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c149 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((209129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85007/250000) (δ := 3343/250000000) (ψ := -904683/1000000) 267 213
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t149 : ((171283998249/10000000000000 : ℚ) : ℝ) ≤ stT267 149 := by
  have hc : ((209079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171283998249/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((209079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c150 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((910699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1064561/10000000) (δ := 13431/1000000000) (ψ := -904683/1000000) 267 213
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t150 : ((46471329119/625000000000 : ℚ) : ℝ) ≤ stT267 150 := by
  have hc : ((910649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46471329119/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((910649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c151 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-294223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5499831/10000000) (δ := 421/31250000) (ψ := -904683/1000000) 267 213
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t151 : ((-29931973209/625000000000 : ℚ) : ℝ) ≤ stT267 151 := by
  have hc : ((-36781/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29931973209/625000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-36781/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c152 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-68169/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1160433/2000000) (δ := 2693/200000000) (ψ := -904683/1000000) 267 214
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t152 : ((-6912059599/125000000000 : ℚ) : ℝ) ≤ stT267 152 := by
  have hc : ((-34087/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6912059599/125000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-34087/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c153 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((841879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14251/100000) (δ := 6719/500000000) (ψ := -904683/1000000) 267 214
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t153 : ((170144584677/2500000000000 : ℚ) : ℝ) ≤ stT267 153 := by
  have hc : ((841829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170144584677/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((841829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c154 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((195359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1461731/5000000) (δ := 2673/200000000) (ψ := -904683/1000000) 267 214
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t154 : ((39351108637/1250000000000 : ℚ) : ℝ) ≤ stT267 154 := by
  have hc : ((97667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39351108637/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((97667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c155 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-970367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452741/625000) (δ := 6719/500000000) (ψ := -904683/1000000) 267 214
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t155 : ((-38972917137/500000000000 : ℚ) : ℝ) ≤ stT267 155 := by
  have hc : ((-970417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38972917137/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-970417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c156 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-97641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2085741/5000000) (δ := 6729/500000000) (ψ := -904683/1000000) 267 215
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t156 : ((-78215419931/10000000000000 : ℚ) : ℝ) ≤ stT267 156 := by
  have hc : ((-97691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78215419931/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-97691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c157 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((499649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9371/1000000) (δ := 2689/200000000) (ψ := -904683/1000000) 267 215
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t157 : ((24921432479/312500000000 : ℚ) : ℝ) ≤ stT267 157 := by
  have hc : ((62453/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24921432479/312500000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((62453/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c158 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-161217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4331801/10000000) (δ := 2689/200000000) (ψ := -904683/1000000) 267 215
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t158 : ((-64148625993/5000000000000 : ℚ) : ℝ) ≤ stT267 158 := by
  have hc : ((-161267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64148625993/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-161267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c159 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-962239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1791193/2500000) (δ := 13551/1000000000) (ψ := -904683/1000000) 267 216
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t159 : ((-190786304007/2500000000000 : ℚ) : ℝ) ≤ stT267 159 := by
  have hc : ((-962289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190786304007/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-962289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c160 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((23117/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1489907/5000000) (δ := 13551/1000000000) (ψ := -904683/1000000) 267 216
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t160 : ((146184904359/5000000000000 : ℚ) : ℝ) ≤ stT267 160 := by
  have hc : ((184911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146184904359/5000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((184911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c161 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((445417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 235809/2000000) (δ := 13451/1000000000) (ψ := -904683/1000000) 267 216
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t161 : ((2193861807/31250000000 : ℚ) : ℝ) ≤ stT267 161 := by
  have hc : ((27837/31250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2193861807/31250000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((27837/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c162 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-263083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1062441/2000000) (δ := 13451/1000000000) (ψ := -904683/1000000) 267 216
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t162 : ((-2067173779/50000000000 : ℚ) : ℝ) ≤ stT267 162 := by
  have hc : ((-65777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2067173779/50000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-65777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c163 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-162031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628803/1000000) (δ := 3361/250000000) (ψ := -904683/1000000) 267 217
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t163 : ((-126920395701/2000000000000 : ℚ) : ℝ) ≤ stT267 163 := by
  have hc : ((-162041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126920395701/2000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-162041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c164 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((79433/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102733/5000000) (δ := 13459/1000000000) (ψ := -904683/1000000) 267 217
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t164 : ((62021807419/1250000000000 : ℚ) : ℝ) ≤ stT267 164 := by
  have hc : ((317707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62021807419/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((317707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c165 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((737857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926133/5000000) (δ := 3361/250000000) (ψ := -904683/1000000) 267 217
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t165 : ((287190636943/5000000000000 : ℚ) : ℝ) ≤ stT267 165 := by
  have hc : ((737807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287190636943/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((737807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c166 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-141139/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5885501/10000000) (δ := 1693/125000000) (ψ := -904683/1000000) 267 217
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t166 : ((-109552937499/2000000000000 : ℚ) : ℝ) ≤ stT267 166 := by
  have hc : ((-141149/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109552937499/2000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-141149/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c167 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-85621/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581339/1000000) (δ := 13367/1000000000) (ψ := -904683/1000000) 267 218
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t167 : ((-4141276319/78125000000 : ℚ) : ℝ) ≤ stT267 167 := by
  have hc : ((-342509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4141276319/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-342509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c168 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((744281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -457087/2500000) (δ := 13467/1000000000) (ψ := -904683/1000000) 267 218
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t168 : ((143546531049/2500000000000 : ℚ) : ℝ) ≤ stT267 168 := by
  have hc : ((744231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143546531049/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((744231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c169 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((10274/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2133131/10000000) (δ := 13467/1000000000) (ψ := -904683/1000000) 267 218
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t169 : ((25287897789/500000000000 : ℚ) : ℝ) ≤ stT267 169 := by
  have hc : ((328743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25287897789/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((328743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c170 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-189081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303559/500000) (δ := 423/31250000) (ψ := -904683/1000000) 267 218
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t170 : ((-58011238491/1000000000000 : ℚ) : ℝ) ≤ stT267 170 := by
  have hc : ((-378187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58011238491/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-378187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c171 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-657831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5721829/10000000) (δ := 13529/1000000000) (ψ := -904683/1000000) 267 219
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t171 : ((-6288684479/125000000000 : ℚ) : ℝ) ≤ stT267 171 := by
  have hc : ((-657881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6288684479/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-657881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c172 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((743919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1829703/10000000) (δ := 13429/1000000000) (ψ := -904683/1000000) 267 219
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t172 : ((141798540387/2500000000000 : ℚ) : ℝ) ≤ stT267 172 := by
  have hc : ((743869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141798540387/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((743869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c173 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((685181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2039861/10000000) (δ := 13529/1000000000) (ψ := -904683/1000000) 267 219
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t173 : ((104178964467/2000000000000 : ℚ) : ℝ) ≤ stT267 173 := by
  have hc : ((685131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104178964467/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((685131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c174 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-706157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5887131/10000000) (δ := 13429/1000000000) (ψ := -904683/1000000) 267 219
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t174 : ((-535374820493/10000000000000 : ℚ) : ℝ) ≤ stT267 174 := by
  have hc : ((-706207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-535374820493/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-706207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c175 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-736201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -599559/1000000) (δ := 6711/500000000) (ψ := -904683/1000000) 267 220
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t175 : ((-556553482179/10000000000000 : ℚ) : ℝ) ≤ stT267 175 := by
  have hc : ((-736251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-556553482179/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-736251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c176 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((15989/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87687/400000) (δ := 6711/500000000) (ψ := -904683/1000000) 267 220
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t176 : ((24102428439/500000000000 : ℚ) : ℝ) ≤ stT267 176 := by
  have hc : ((63951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24102428439/500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((63951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c177 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((402269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1589747/10000000) (δ := 13481/1000000000) (ψ := -904683/1000000) 267 220
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t177 : ((37793136703/625000000000 : ℚ) : ℝ) ≤ stT267 177 := by
  have hc : ((100561/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37793136703/625000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((100561/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c178 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-107813/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1337577/2500000) (δ := 6711/500000000) (ψ := -904683/1000000) 267 220
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t178 : ((-20204197209/500000000000 : ℚ) : ℝ) ≤ stT267 178 := by
  have hc : ((-107823/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20204197209/500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-107823/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c179 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-22007/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165453/250000) (δ := 2683/200000000) (ψ := -904683/1000000) 267 221
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t179 : ((-16449758347/250000000000 : ℚ) : ℝ) ≤ stT267 179 := by
  have hc : ((-88033/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16449758347/250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-88033/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c180 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((399531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2899477/10000000) (δ := 843/62500000) (ψ := -904683/1000000) 267 221
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t180 : ((59551032151/2000000000000 : ℚ) : ℝ) ≤ stT267 180 := by
  have hc : ((399481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59551032151/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((399481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c181 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((949411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 399303/5000000) (δ := 2683/200000000) (ψ := -904683/1000000) 267 221
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t181 : ((352827167567/5000000000000 : ℚ) : ℝ) ≤ stT267 181 := by
  have hc : ((949361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352827167567/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((949361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c182 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-108973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559533/1250000) (δ := 2683/200000000) (ψ := -904683/1000000) 267 221
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t182 : ((-32317907/2000000000 : ℚ) : ℝ) ≤ stT267 182 := by
  have hc : ((-54499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32317907/2000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-54499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c183 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-993741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7574133/10000000) (δ := 419/31250000) (ψ := -904683/1000000) 267 222
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t183 : ((-367316085301/5000000000000 : ℚ) : ℝ) ≤ stT267 183 := by
  have hc : ((-993791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367316085301/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-993791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c184 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-1907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157461/400000) (δ := 419/31250000) (ψ := -904683/1000000) 267 222
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t184 : ((-35607243/125000000000 : ℚ) : ℝ) ≤ stT267 184 := by
  have hc : ((-483/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35607243/125000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-483/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c185 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((99189/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19913/625000) (δ := 2679/200000000) (ψ := -904683/1000000) 267 222
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t185 : ((2278795793/31250000000 : ℚ) : ℝ) ≤ stT267 185 := by
  have hc : ((6199/6250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2278795793/31250000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((6199/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c186 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((256013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3279751/10000000) (δ := 2679/200000000) (ψ := -904683/1000000) 267 222
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t186 : ((37536206061/2000000000000 : ℚ) : ℝ) ≤ stT267 186 := by
  have hc : ((255963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37536206061/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((255963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c187 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-921823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3429443/5000000) (δ := 2679/200000000) (ψ := -904683/1000000) 267 222
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t187 : ((-674140834329/10000000000000 : ℚ) : ℝ) ≤ stT267 187 := by
  have hc : ((-921873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-674140834329/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-921873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c188 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-129571/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52891/100000) (δ := 27/2000000) (ψ := -904683/1000000) 267 223
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t188 : ((-7560678891/200000000000 : ℚ) : ℝ) ≤ stT267 188 := by
  have hc : ((-259167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7560678891/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-259167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c189 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((765371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349589/2000000) (δ := 13503/1000000000) (ψ := -904683/1000000) 267 223
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t189 : ((17396511651/312500000000 : ℚ) : ℝ) ≤ stT267 189 := by
  have hc : ((765321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17396511651/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((765321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c190 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((151701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443613/2500000) (δ := 67/5000000) (ψ := -904683/1000000) 267 223
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t190 : ((27512044979/500000000000 : ℚ) : ℝ) ≤ stT267 190 := by
  have hc : ((151691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27512044979/500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((151691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c191 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-514629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5278427/10000000) (δ := 13503/1000000000) (ψ := -904683/1000000) 267 223
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t191 : ((-14896354297/400000000000 : ℚ) : ℝ) ≤ stT267 191 := by
  have hc : ((-514679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14896354297/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-514679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c192 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-934471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3471959/5000000) (δ := 1351/100000000) (ψ := -904683/1000000) 267 224
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t192 : ((-84304073931/1250000000000 : ℚ) : ℝ) ≤ stT267 192 := by
  have hc : ((-934521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84304073931/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-934521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c193 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((89633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3476389/10000000) (δ := 1351/100000000) (ψ := -904683/1000000) 267 224
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t193 : ((1612529563/125000000000 : ℚ) : ℝ) ≤ stT267 193 := by
  have hc : ((11201/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1612529563/125000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((11201/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c194 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((999943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26749/10000000) (δ := 1351/100000000) (ψ := -904683/1000000) 267 224
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t194 : ((358940589247/5000000000000 : ℚ) : ℝ) ≤ stT267 194 := by
  have hc : ((999893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358940589247/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((999893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c195 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((20723/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 681027/2000000) (δ := 13393/1000000000) (ψ := -904683/1000000) 267 224
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t195 : ((3709112463/250000000000 : ℚ) : ℝ) ≤ stT267 195 := by
  have hc : ((10359/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3709112463/250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((10359/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c196 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-915597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 852433/1250000) (δ := 13493/1000000000) (ψ := -904683/1000000) 267 224
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t196 : ((-327016916521/5000000000000 : ℚ) : ℝ) ≤ stT267 196 := by
  have hc : ((-915647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327016916521/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-915647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c197 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-585757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219661/400000) (δ := 6743/500000000) (ψ := -904683/1000000) 267 225
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t197 : ((-417370499097/10000000000000 : ℚ) : ℝ) ≤ stT267 197 := by
  have hc : ((-585807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-417370499097/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-585807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c198 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((663949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -527943/2500000) (δ := 6693/500000000) (ψ := -904683/1000000) 267 225
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t198 : ((471812438431/10000000000000 : ℚ) : ℝ) ≤ stT267 198 := by
  have hc : ((663899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471812438431/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((663899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c199 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((438699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15637/125000) (δ := 13517/1000000000) (ψ := -904683/1000000) 267 225
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t199 : ((155483831897/2500000000000 : ℚ) : ℝ) ≤ stT267 199 := by
  have hc : ((219337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155483831897/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((219337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c200 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-264731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4596803/10000000) (δ := 6743/500000000) (ψ := -904683/1000000) 267 225
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t200 : ((-187228498567/10000000000000 : ℚ) : ℝ) ≤ stT267 200 := by
  have hc : ((-264781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187228498567/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-264781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c201 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-199917/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7781937/10000000) (δ := 13379/1000000000) (ψ := -904683/1000000) 267 226
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t201 : ((-70508854871/1000000000000 : ℚ) : ℝ) ≤ stT267 201 := by
  have hc : ((-199927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70508854871/1000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-199927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c202 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-5381/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893867/2000000) (δ := 13479/1000000000) (ψ := -904683/1000000) 267 226
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t202 : ((-7573880671/500000000000 : ℚ) : ℝ) ≤ stT267 202 := by
  have hc : ((-21529/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7573880671/500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-21529/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c203 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((891927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1173019/10000000) (δ := 3381/250000000) (ψ := -904683/1000000) 267 226
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t203 : ((312987287487/5000000000000 : ℚ) : ℝ) ≤ stT267 203 := by
  have hc : ((891877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312987287487/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((891877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c204 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((665353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 526769/2500000) (δ := 3381/250000000) (ψ := -904683/1000000) 267 226
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t204 : ((23290262121/500000000000 : ℚ) : ℝ) ≤ stT267 204 := by
  have hc : ((665303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23290262121/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((665303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c205 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-546069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5371151/10000000) (δ := 3381/250000000) (ψ := -904683/1000000) 267 226
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t205 : ((-381426439289/10000000000000 : ℚ) : ℝ) ≤ stT267 205 := by
  have hc : ((-546119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381426439289/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-546119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c206 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-953503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -443039/625000) (δ := 13431/1000000000) (ψ := -904683/1000000) 267 227
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t206 : ((-332186397951/5000000000000 : ℚ) : ℝ) ≤ stT267 206 := by
  have hc : ((-953553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332186397951/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-953553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c207 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((28317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3856189/10000000) (δ := 421/31250000) (ψ := -904683/1000000) 267 227
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t207 : ((2455865227/1250000000000 : ℚ) : ℝ) ≤ stT267 207 := by
  have hc : ((28267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2455865227/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((28267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c208 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((967481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -319653/5000000) (δ := 3343/250000000) (ψ := -904683/1000000) 267 227
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t208 : ((5366339757/80000000000 : ℚ) : ℝ) ≤ stT267 208 := by
  have hc : ((967431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5366339757/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((967431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c209 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((32451/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1281079/5000000) (δ := 13531/1000000000) (ψ := -904683/1000000) 267 227
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t209 : ((89778597631/2500000000000 : ℚ) : ℝ) ≤ stT267 209 := by
  have hc : ((259583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89778597631/2500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((259583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c210 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-665779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1149667/2000000) (δ := 421/31250000) (ψ := -904683/1000000) 267 227
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t210 : ((-229732977357/5000000000000 : ℚ) : ℝ) ≤ stT267 210 := by
  have hc : ((-665829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229732977357/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-665829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c211 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-910563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3394301/5000000) (δ := 6769/500000000) (ψ := -904683/1000000) 267 228
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t211 : ((-626892396977/10000000000000 : ℚ) : ℝ) ≤ stT267 211 := by
  have hc : ((-910613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-626892396977/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-910613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c212 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((58743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -908149/2500000) (δ := 2693/200000000) (ψ := -904683/1000000) 267 228
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t212 : ((10081909959/1250000000000 : ℚ) : ℝ) ≤ stT267 212 := by
  have hc : ((29359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10081909959/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((29359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c213 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((122593/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -491407/10000000) (δ := 6769/500000000) (ψ := -904683/1000000) 267 228
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t213 : ((83994970059/1250000000000 : ℚ) : ℝ) ≤ stT267 213 := by
  have hc : ((490347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83994970059/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((490347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c214 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((30879/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329387/1250000) (δ := 6719/500000000) (ψ := -904683/1000000) 267 228
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t214 : ((33770056019/1000000000000 : ℚ) : ℝ) ≤ stT267 214 := by
  have hc : ((247007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33770056019/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((247007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c215 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-5323/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5746981/10000000) (δ := 6719/500000000) (ψ := -904683/1000000) 267 228
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t215 : ((-3630532183/80000000000 : ℚ) : ℝ) ≤ stT267 215 := by
  have hc : ((-26617/40000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3630532183/80000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-26617/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c216 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-922539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1372703/2000000) (δ := 6773/500000000) (ψ := -904683/1000000) 267 229
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t216 : ((-313871235923/5000000000000 : ℚ) : ℝ) ≤ stT267 216 := by
  have hc : ((-922589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313871235923/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-922589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c217 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((58603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9451/25000) (δ := 13457/1000000000) (ψ := -904683/1000000) 267 229
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t217 : ((9937088183/2500000000000 : ℚ) : ℝ) ≤ stT267 217 := by
  have hc : ((58553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9937088183/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((58553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c218 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((959781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142287/2000000) (δ := 13357/1000000000) (ψ := -904683/1000000) 267 229
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t218 : ((130002282067/2000000000000 : ℚ) : ℝ) ≤ stT267 218 := by
  have hc : ((959731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130002282067/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((959731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c219 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((295941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292939/1250000) (δ := 13457/1000000000) (ψ := -904683/1000000) 267 229
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t219 : ((49990347523/1250000000000 : ℚ) : ℝ) ≤ stT267 219 := by
  have hc : ((73979/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49990347523/1250000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((73979/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c220 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-550537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5384509/10000000) (δ := 6723/500000000) (ψ := -904683/1000000) 267 229
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t220 : ((-1856028777/50000000000 : ℚ) : ℝ) ≤ stT267 220 := by
  have hc : ((-550587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1856028777/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-550587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c221 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-487607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7296209/10000000) (δ := 271/20000000) (ψ := -904683/1000000) 267 230
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t221 : ((-20501055021/312500000000 : ℚ) : ℝ) ≤ stT267 221 := by
  have hc : ((-30477/31250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20501055021/312500000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-30477/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c222 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-141809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4282713/10000000) (δ := 13353/1000000000) (ψ := -904683/1000000) 267 230
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t222 : ((-95209660863/10000000000000 : ℚ) : ℝ) ≤ stT267 222 := by
  have hc : ((-141859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95209660863/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-141859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c223 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((871237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1282701/10000000) (δ := 13353/1000000000) (ψ := -904683/1000000) 267 230
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t223 : ((583389503363/10000000000000 : ℚ) : ℝ) ≤ stT267 223 := by
  have hc : ((871187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583389503363/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((871187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c224 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((48537/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 851947/5000000) (δ := 269/20000000) (ψ := -904683/1000000) 267 230
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t224 : ((259424433463/5000000000000 : ℚ) : ℝ) ≤ stT267 224 := by
  have hc : ((388271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259424433463/5000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((388271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c225 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-147801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2338603/5000000) (δ := 269/20000000) (ψ := -904683/1000000) 267 230
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t225 : ((-49275357971/2500000000000 : ℚ) : ℝ) ≤ stT267 225 := by
  have hc : ((-73913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49275357971/2500000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-73913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c226 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-199249/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909317/2500000) (δ := 537/20000000) (ψ := -904683/1000000) 267 230
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t226 : ((-132545293469/2000000000000 : ℚ) : ℝ) ≤ stT267 226 := by
  have hc : ((-199259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132545293469/2000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-199259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c227 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-460593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5123649/10000000) (δ := 167/12500000) (ψ := -904683/1000000) 267 231
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t227 : ((-76434953633/2500000000000 : ℚ) : ℝ) ≤ stT267 227 := by
  have hc : ((-460643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76434953633/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-460643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c228 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((160089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1094793/5000000) (δ := 167/12500000) (ψ := -904683/1000000) 267 231
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t228 : ((106013223349/2500000000000 : ℚ) : ℝ) ≤ stT267 228 := by
  have hc : ((320153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106013223349/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((320153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c229 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((957479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731661/10000000) (δ := 167/12500000) (ψ := -904683/1000000) 267 231
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t229 : ((316343158461/5000000000000 : ℚ) : ℝ) ≤ stT267 229 := by
  have hc : ((957429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316343158461/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((957429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c230 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((114481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3640159/10000000) (δ := 673/50000000) (ψ := -904683/1000000) 267 231
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t230 : ((3772675639/500000000000 : ℚ) : ℝ) ≤ stT267 230 := by
  have hc : ((114431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3772675639/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((114431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c231 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-864231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6536041/10000000) (δ := 673/50000000) (ψ := -904683/1000000) 267 231
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t231 : ((-17770481641/312500000000 : ℚ) : ℝ) ≤ stT267 231 := by
  have hc : ((-864281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17770481641/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-864281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c232 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-405143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628859/1000000) (δ := 423/31250000) (ψ := -904683/1000000) 267 232
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t232 : ((-16625385159/312500000000 : ℚ) : ℝ) ≤ stT267 232 := by
  have hc : ((-25323/31250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16625385159/312500000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-25323/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c233 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((202347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -683521/2000000) (δ := 13467/1000000000) (ψ := -904683/1000000) 267 232
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t233 : ((132529012937/10000000000000 : ℚ) : ℝ) ≤ stT267 233 := by
  have hc : ((202297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132529012937/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((202297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c234 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((487557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -558903/10000000) (δ := 13367/1000000000) (ψ := -904683/1000000) 267 232
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t234 : ((1991933869/31250000000 : ℚ) : ℝ) ≤ stT267 234 := by
  have hc : ((121883/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1991933869/31250000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((121883/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c235 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((152441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71487/312500) (δ := 13367/1000000000) (ψ := -904683/1000000) 267 232
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t235 : ((24858344637/625000000000 : ℚ) : ℝ) ≤ stT267 235 := by
  have hc : ((304857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24858344637/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((304857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c236 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-115001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5121989/10000000) (δ := 3359/250000000) (ψ := -904683/1000000) 267 232
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t236 : ((-29946985103/1000000000000 : ℚ) : ℝ) ≤ stT267 236 := by
  have hc : ((-230027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29946985103/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-230027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c237 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-499673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60653/78125) (δ := 13429/1000000000) (ψ := -904683/1000000) 267 233
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t237 : ((-16229441493/250000000000 : ℚ) : ℝ) ≤ stT267 237 := by
  have hc : ((-249849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16229441493/250000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-249849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c238 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-399007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198123/400000) (δ := 6687/500000000) (ψ := -904683/1000000) 267 233
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t238 : ((-64667585907/2500000000000 : ℚ) : ℝ) ≤ stT267 238 := by
  have hc : ((-399057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64667585907/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-399057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c239 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((651129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1077157/5000000) (δ := 6737/500000000) (ψ := -904683/1000000) 267 233
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t239 : ((210573923417/5000000000000 : ℚ) : ℝ) ≤ stT267 239 := by
  have hc : ((651079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210573923417/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((651079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c240 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((968139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126553/2000000) (δ := 13429/1000000000) (ψ := -904683/1000000) 267 233
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t240 : ((624898545233/10000000000000 : ℚ) : ℝ) ≤ stT267 240 := by
  have hc : ((968089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((624898545233/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((968089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c241 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((103009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340823/1000000) (δ := 13429/1000000000) (ψ := -904683/1000000) 267 233
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t241 : ((2073055047/156250000000 : ℚ) : ℝ) ≤ stT267 241 := by
  have hc : ((12873/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2073055047/156250000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((12873/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c242 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-391069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3086107/5000000) (δ := 13429/1000000000) (ψ := -904683/1000000) 267 233
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t242 : ((-5028100011/100000000000 : ℚ) : ℝ) ≤ stT267 242 := by
  have hc : ((-195547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5028100011/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-195547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c243 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-28427/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6783179/10000000) (δ := 6741/500000000) (ψ := -904683/1000000) 267 234
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t243 : ((-291791220357/5000000000000 : ℚ) : ℝ) ≤ stT267 243 := by
  have hc : ((-454857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291791220357/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-454857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c244 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-45943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404189/1000000) (δ := 6741/500000000) (ψ := -904683/1000000) 267 234
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t244 : ((-5888805741/2000000000000 : ℚ) : ℝ) ≤ stT267 244 := by
  have hc : ((-45993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5888805741/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-45993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c245 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((432727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1311849/10000000) (δ := 26821/1000000000) (ψ := -904683/1000000) 267 234
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t245 : ((34555365369/625000000000 : ℚ) : ℝ) ≤ stT267 245 := by
  have hc : ((216351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34555365369/625000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((216351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c246 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((845741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175889/1250000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 234
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t246 : ((67399035627/1250000000000 : ℚ) : ℝ) ≤ stT267 246 := by
  have hc : ((845691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67399035627/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((845691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c247 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-75143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2057513/5000000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 234
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t247 : ((-9568835601/2000000000000 : ℚ) : ℝ) ≤ stT267 247 := by
  have hc : ((-75193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9568835601/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-75193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c248 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-914391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6811993/10000000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 234
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t248 : ((-580670949441/10000000000000 : ℚ) : ℝ) ≤ stT267 248 := by
  have hc : ((-914441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-580670949441/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-914441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c249 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-791437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6209883/10000000) (δ := 13389/1000000000) (ψ := -904683/1000000) 267 235
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t249 : ((-20063403963/400000000000 : ℚ) : ℝ) ≤ stT267 249 := by
  have hc : ((-791487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20063403963/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-791487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c250 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((78181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -883619/2500000) (δ := 13489/1000000000) (ψ := -904683/1000000) 267 235
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t250 : ((2471507649/250000000000 : ℚ) : ℝ) ≤ stT267 250 := by
  have hc : ((19539/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2471507649/250000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((19539/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c251 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((470041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108727/1250000) (δ := 13489/1000000000) (ψ := -904683/1000000) 267 235
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t251 : ((144859023/2441406250 : ℚ) : ℝ) ≤ stT267 251 := by
  have hc : ((14688/15625 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144859023/2441406250 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((14688/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c252 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((15119/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 178423/1000000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 235
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t252 : ((238085823/5000000000 : ℚ) : ℝ) ≤ stT267 252 := by
  have hc : ((7559/10000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238085823/5000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((7559/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c253 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-39797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4427797/10000000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 235
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t253 : ((-5005292373/400000000000 : ℚ) : ℝ) ≤ stT267 253 := by
  have hc : ((-39807/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5005292373/400000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-39807/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c254 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-950109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7060951/10000000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 235
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t254 : ((-2328839709/39062500000 : ℚ) : ℝ) ≤ stT267 254 := by
  have hc : ((-950159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2328839709/39062500000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-950159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c255 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-743899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1506051/2500000) (δ := 3349/250000000) (ψ := -904683/1000000) 267 236
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t255 : ((-18635178501/400000000000 : ℚ) : ℝ) ≤ stT267 255 := by
  have hc : ((-743949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18635178501/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-743949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c256 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((204669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -852919/2500000) (δ := 13407/1000000000) (ψ := -904683/1000000) 267 236
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t256 : ((204619/16000000 : ℚ) : ℝ) ≤ stT267 256 := by
  have hc : ((204619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204619/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((204619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c257 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((948051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10117/125000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 236
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t257 : ((295672979891/5000000000000 : ℚ) : ℝ) ≤ stT267 257 := by
  have hc : ((948001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295672979891/5000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((948001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c258 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((151261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445719/2500000) (δ := 3349/250000000) (ψ := -904683/1000000) 267 236
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t258 : ((23541159393/500000000000 : ℚ) : ℝ) ≤ stT267 258 := by
  have hc : ((151251/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23541159393/500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((151251/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c259 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-43587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43651/100000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 236
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t259 : ((-5418284263/500000000000 : ℚ) : ℝ) ≤ stT267 259 := by
  have hc : ((-87199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5418284263/500000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-87199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c260 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-933537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3468689/5000000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 236
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t260 : ((-289493192069/5000000000000 : ℚ) : ℝ) ≤ stT267 260 := by
  have hc : ((-933587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289493192069/5000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-933587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c261 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-395511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6208187/10000000) (δ := 27/2000000) (ψ := -904683/1000000) 267 237
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t261 : ((-3060385637/62500000000 : ℚ) : ℝ) ≤ stT267 261 := by
  have hc : ((-24721/31250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3060385637/62500000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-24721/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c262 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((108343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9139/25000) (δ := 401/10000000) (ψ := -904683/1000000) 267 237
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t262 : ((33451815993/5000000000000 : ℚ) : ℝ) ≤ stT267 262 := by
  have hc : ((108293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33451815993/5000000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((108293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c263 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((451283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1112759/10000000) (δ := 27/2000000) (ψ := -904683/1000000) 267 237
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t263 : ((69564353877/1250000000000 : ℚ) : ℝ) ≤ stT267 263 := by
  have hc : ((225629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69564353877/1250000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((225629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c264 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((842877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1420471/10000000) (δ := 40203/1000000000) (ψ := -904683/1000000) 267 237
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t264 : ((518723776939/10000000000000 : ℚ) : ℝ) ≤ stT267 264 := by
  have hc : ((842827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518723776939/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((842827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c265 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-6839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 493011/1250000) (δ := 13403/1000000000) (ψ := -904683/1000000) 267 237
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t265 : ((-528985643/1250000000000 : ℚ) : ℝ) ≤ stT267 265 := by
  have hc : ((-6889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528985643/1250000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-6889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c266 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-212039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6458227/10000000) (δ := 13503/1000000000) (ψ := -904683/1000000) 267 237
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t266 : ((-13001725671/250000000000 : ℚ) : ℝ) ≤ stT267 266 := by
  have hc : ((-424103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13001725671/250000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-424103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c267 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-903229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1686269/2500000) (δ := 1351/100000000) (ψ := -904683/1000000) 267 238
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t267 : ((-552798618489/10000000000000 : ℚ) : ℝ) ≤ stT267 267 := by
  have hc : ((-903279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552798618489/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-903279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c268 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-103/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4249761/10000000) (δ := 1341/100000000) (ψ := -904683/1000000) 267 238
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t268 : ((-3073329/390625000 : ℚ) : ℝ) ≤ stT267 268 := by
  have hc : ((-161/1250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3073329/390625000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-161/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c269 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((380647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -440931/2500000) (δ := 1341/100000000) (ψ := -904683/1000000) 267 238
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t269 : ((11603451981/250000000000 : ℚ) : ℝ) ≤ stT267 269 := by
  have hc : ((190311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11603451981/250000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((190311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c270 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((479797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 713101/10000000) (δ := 13493/1000000000) (ψ := -904683/1000000) 267 238
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t270 : ((3649745547/62500000000 : ℚ) : ℝ) ≤ stT267 270 := by
  have hc : ((119943/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3649745547/62500000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((119943/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c271 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((294071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1590391/5000000) (δ := 13393/1000000000) (ψ := -904683/1000000) 267 238
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t271 : ((5581400643/312500000000 : ℚ) : ℝ) ≤ stT267 271 := by
  have hc : ((294021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5581400643/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((294021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c272 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-632619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2819659/5000000) (δ := 13393/1000000000) (ψ := -904683/1000000) 267 238
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t272 : ((-19180626073/500000000000 : ℚ) : ℝ) ≤ stT267 272 := by
  have hc : ((-632669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19180626073/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-632669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c273 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-99559/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95239/125000) (δ := 13517/1000000000) (ψ := -904683/1000000) 267 239
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t273 : ((-3766182537/62500000000 : ℚ) : ℝ) ≤ stT267 273 := by
  have hc : ((-24891/25000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3766182537/62500000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-24891/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c274 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-239973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5178473/10000000) (δ := 13517/1000000000) (ψ := -904683/1000000) 267 239
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t274 : ((-72494155877/2500000000000 : ℚ) : ℝ) ≤ stT267 274 := by
  have hc : ((-119999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72494155877/2500000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-119999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c275 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((454723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1373419/5000000) (δ := 6743/500000000) (ψ := -904683/1000000) 267 239
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t275 : ((137088910903/5000000000000 : ℚ) : ℝ) ≤ stT267 275 := by
  have hc : ((454673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137088910903/5000000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((454673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c276 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((15494/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161973/5000000) (δ := 13417/1000000000) (ψ := -904683/1000000) 267 239
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t276 : ((298426165407/5000000000000 : ℚ) : ℝ) ≤ stT267 276 := by
  have hc : ((495783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298426165407/5000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((495783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c277 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((83797/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2090201/10000000) (δ := 6693/500000000) (ψ := -904683/1000000) 267 239
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t277 : ((201379672083/5000000000000 : ℚ) : ℝ) ≤ stT267 277 := by
  have hc : ((335163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201379672083/5000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((335163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c278 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-225489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1123901/2500000) (δ := 6693/500000000) (ψ := -904683/1000000) 267 239
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t278 : ((-135269496179/10000000000000 : ℚ) : ℝ) ≤ stT267 278 := by
  have hc : ((-225539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135269496179/10000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-225539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c279 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-463463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689233/1000000) (δ := 13517/1000000000) (ψ := -904683/1000000) 267 239
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t279 : ((-433567677/7812500000 : ℚ) : ℝ) ≤ stT267 279 := by
  have hc : ((-14484/15625 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433567677/7812500000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-14484/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c280 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-210389/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1285477/2000000) (δ := 541/40000000) (ψ := -904683/1000000) 267 240
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t280 : ((-50295636969/1000000000000 : ℚ) : ℝ) ≤ stT267 280 := by
  have hc : ((-420803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50295636969/1000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-420803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c281 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-12071/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011937/2500000) (δ := 6689/500000000) (ψ := -904683/1000000) 267 240
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t281 : ((-288336477/100000000000 : ℚ) : ℝ) ≤ stT267 281 := by
  have hc : ((-24167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288336477/100000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-24167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c282 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((195861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1676521/10000000) (δ := 6689/500000000) (ψ := -904683/1000000) 267 240
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t282 : ((233252038227/5000000000000 : ℚ) : ℝ) ≤ stT267 282 := by
  have hc : ((391697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233252038227/5000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((391697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c283 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((240639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85787/1250000) (δ := 541/40000000) (ψ := -904683/1000000) 267 240
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t283 : ((143037535407/2500000000000 : ℚ) : ℝ) ≤ stT267 283 := by
  have hc : ((481253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143037535407/2500000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((481253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c284 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((173543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608167/2000000) (δ := 6689/500000000) (ψ := -904683/1000000) 267 240
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t284 : ((5148192301/250000000000 : ℚ) : ℝ) ≤ stT267 284 := by
  have hc : ((86759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5148192301/250000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((86759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c285 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-551379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5387031/10000000) (δ := 537/40000000) (ψ := -904683/1000000) 267 240
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t285 : ((-326638416721/10000000000000 : ℚ) : ℝ) ≤ stT267 285 := by
  have hc : ((-551429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326638416721/10000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-551429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c286 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-998671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7725083/10000000) (δ := 6689/500000000) (ψ := -904683/1000000) 267 240
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t286 : ((-590556710673/10000000000000 : ℚ) : ℝ) ≤ stT267 286 := by
  have hc : ((-998721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-590556710673/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-998721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c287 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-31843/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2826519/5000000) (δ := 1679/125000000) (ψ := -904683/1000000) 267 241
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t287 : ((-18797825431/500000000000 : ℚ) : ℝ) ≤ stT267 287 := by
  have hc : ((-63691/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18797825431/500000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-63691/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c288 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((59003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166567/500000) (δ := 13471/1000000000) (ψ := -904683/1000000) 267 241
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t288 : ((13904178831/1000000000000 : ℚ) : ℝ) ≤ stT267 288 := by
  have hc : ((117981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13904178831/1000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((117981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c289 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((918289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1017651/10000000) (δ := 1679/125000000) (ψ := -904683/1000000) 267 241
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t289 : ((108028063633/2000000000000 : ℚ) : ℝ) ≤ stT267 289 := by
  have hc : ((918239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108028063633/2000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((918239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c290 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((27193/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 644047/5000000) (δ := 13371/1000000000) (ψ := -904683/1000000) 267 241
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t290 : ((12773884743/250000000000 : ℚ) : ℝ) ≤ stT267 290 := by
  have hc : ((435063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12773884743/250000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((435063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c291 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((68021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3585829/10000000) (δ := 13471/1000000000) (ψ := -904683/1000000) 267 241
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t291 : ((996498379/125000000000 : ℚ) : ℝ) ≤ stT267 291 := by
  have hc : ((16999/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((996498379/125000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((16999/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c292 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-43933/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1175151/2000000) (δ := 1679/125000000) (ψ := -904683/1000000) 267 241
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t292 : ((-102846735867/2500000000000 : ℚ) : ℝ) ≤ stT267 292 := by
  have hc : ((-351489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102846735867/2500000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-351489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c293 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-62039/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7550159/10000000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 242
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t293 : ((-289963549759/5000000000000 : ℚ) : ℝ) ≤ stT267 293 := by
  have hc : ((-496337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289963549759/5000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-496337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c294 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-513769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65949/125000) (δ := 13439/1000000000) (ψ := -904683/1000000) 267 242
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t294 : ((-74916351657/2500000000000 : ℚ) : ℝ) ≤ stT267 294 := by
  have hc : ((-513819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74916351657/2500000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-513819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c295 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((358867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3009357/10000000) (δ := 13439/1000000000) (ψ := -904683/1000000) 267 242
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t295 : ((104455575687/5000000000000 : ℚ) : ℝ) ≤ stT267 295 := by
  have hc : ((358817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104455575687/5000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((358817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c296 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((955281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75047/1000000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 242
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t296 : ((277608277989/5000000000000 : ℚ) : ℝ) ≤ stT267 296 := by
  have hc : ((955231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277608277989/5000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((955231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c297 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((825153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1500807/10000000) (δ := 13439/1000000000) (ψ := -904683/1000000) 267 242
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t297 : ((239386308287/5000000000000 : ℚ) : ℝ) ≤ stT267 297 := by
  have hc : ((825103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239386308287/5000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((825103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c298 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((72941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149779/400000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 242
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t298 : ((10556147511/2500000000000 : ℚ) : ℝ) ≤ stT267 298 := by
  have hc : ((72891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10556147511/2500000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((72891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c299 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-183037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2990333/5000000) (δ := 1683/125000000) (ψ := -904683/1000000) 267 242
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t299 : ((-42344108637/1000000000000 : ℚ) : ℝ) ≤ stT267 299 := by
  have hc : ((-366099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42344108637/1000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-366099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c300 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-123739/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7498581/10000000) (δ := 6723/500000000) (ψ := -904683/1000000) 267 243
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t300 : ((-285777775331/5000000000000 : ℚ) : ℝ) ≤ stT267 300 := by
  have hc : ((-494981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285777775331/5000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-494981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c301 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-514233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211091/400000) (δ := 13457/1000000000) (ψ := -904683/1000000) 267 243
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t301 : ((-296428092653/10000000000000 : ℚ) : ℝ) ≤ stT267 301 := by
  have hc : ((-514283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296428092653/10000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-514283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c302 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((338641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3063311/10000000) (δ := 13457/1000000000) (ψ := -904683/1000000) 267 243
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t302 : ((38967422417/2000000000000 : ℚ) : ℝ) ≤ stT267 302 := by
  have hc : ((338591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38967422417/2000000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((338591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c303 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((941859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -856689/10000000) (δ := 6723/500000000) (ψ := -904683/1000000) 267 243
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t303 : ((135263550389/2500000000000 : ℚ) : ℝ) ≤ stT267 303 := by
  have hc : ((941809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135263550389/2500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((941809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c304 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((171843/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1342657/10000000) (δ := 6773/500000000) (ψ := -904683/1000000) 267 243
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t304 : ((98552926987/2000000000000 : ℚ) : ℝ) ≤ stT267 304 := by
  have hc : ((171833/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98552926987/2000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((171833/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c305 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((156263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3534727/10000000) (δ := 6773/500000000) (ψ := -904683/1000000) 267 243
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t305 : ((44723625687/5000000000000 : ℚ) : ℝ) ≤ stT267 305 := by
  have hc : ((156213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44723625687/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((156213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c306 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-164299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5719721/10000000) (δ := 13357/1000000000) (ψ := -904683/1000000) 267 243
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t306 : ((-93930640713/2500000000000 : ℚ) : ℝ) ≤ stT267 306 := by
  have hc : ((-328623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93930640713/2500000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-328623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c307 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-124981/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7810457/10000000) (δ := 269/20000000) (ψ := -904683/1000000) 267 244
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t307 : ((-285336392719/5000000000000 : ℚ) : ℝ) ≤ stT267 307 := by
  have hc : ((-499949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285336392719/5000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-499949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c308 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-39547/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5639747/10000000) (δ := 269/20000000) (ψ := -904683/1000000) 267 244
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t308 : ((-180286239003/5000000000000 : ℚ) : ℝ) ≤ stT267 308 := by
  have hc : ((-316401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180286239003/5000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-316401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c309 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((179401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1738023/5000000) (δ := 271/20000000) (ψ := -904683/1000000) 267 244
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t309 : ((1275364961/125000000000 : ℚ) : ℝ) ≤ stT267 309 := by
  have hc : ((179351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1275364961/125000000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((179351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c310 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((863947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1319353/10000000) (δ := 13353/1000000000) (ψ := -904683/1000000) 267 244
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t310 : ((490659804017/10000000000000 : ℚ) : ℝ) ≤ stT267 310 := by
  have hc : ((863897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((490659804017/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((863897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c311 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((236333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6488/78125) (δ := 269/20000000) (ψ := -904683/1000000) 267 244
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t311 : ((268009661127/5000000000000 : ℚ) : ℝ) ≤ stT267 311 := by
  have hc : ((472641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268009661127/5000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((472641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c312 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((372301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2973273/10000000) (δ := 13453/1000000000) (ψ := -904683/1000000) 267 244
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t312 : ((105372718319/5000000000000 : ℚ) : ℝ) ≤ stT267 312 := by
  have hc : ((372251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105372718319/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((372251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c313 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-455481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5109273/10000000) (δ := 13453/1000000000) (ψ := -904683/1000000) 267 244
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t313 : ((-128740804627/5000000000000 : ℚ) : ℝ) ≤ stT267 313 := by
  have hc : ((-455531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128740804627/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-455531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c314 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-242461/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113101/156250) (δ := 269/20000000) (ψ := -904683/1000000) 267 244
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t314 : ((-273671595351/5000000000000 : ℚ) : ℝ) ≤ stT267 314 := by
  have hc : ((-484947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273671595351/5000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-484947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c315 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-823767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6347049/10000000) (δ := 673/50000000) (ψ := -904683/1000000) 267 245
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t315 : ((-464168979029/10000000000000 : ℚ) : ℝ) ≤ stT267 315 := by
  have hc : ((-823817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464168979029/10000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-823817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c316 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-759/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4231341/10000000) (δ := 673/50000000) (ψ := -904683/1000000) 267 245
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t316 : ((-427146691/62500000000 : ℚ) : ℝ) ≤ stT267 316 := by
  have hc : ((-12149/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427146691/62500000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-12149/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c317 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((165193/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16979/80000) (δ := 167/12500000) (ψ := -904683/1000000) 267 245
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t317 : ((37109781491/1000000000000 : ℚ) : ℝ) ≤ stT267 317 := by
  have hc : ((330361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37109781491/1000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((330361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c318 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((31249/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20017/10000000) (δ := 167/12500000) (ψ := -904683/1000000) 267 245
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t318 : ((70090752087/1250000000000 : ℚ) : ℝ) ≤ stT267 318 := by
  have hc : ((499959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70090752087/1250000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((499959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c319 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((8433/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2075799/10000000) (δ := 13543/1000000000) (ψ := -904683/1000000) 267 245
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t319 : ((9442438607/250000000000 : ℚ) : ℝ) ≤ stT267 319 := by
  have hc : ((67459/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9442438607/250000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((67459/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c320 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-23759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4164941/10000000) (δ := 167/12500000) (ψ := -904683/1000000) 267 245
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t320 : ((-26577345231/5000000000000 : ℚ) : ℝ) ≤ stT267 320 := by
  have hc : ((-47543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26577345231/5000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-47543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c321 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-400293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3123837/5000000) (δ := 13543/1000000000) (ψ := -904683/1000000) 267 245
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t321 : ((-55858972607/1250000000000 : ℚ) : ℝ) ≤ stT267 321 := by
  have hc : ((-200159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55858972607/1250000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-200159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c322 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-982389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7384097/10000000) (δ := 2687/200000000) (ψ := -904683/1000000) 267 246
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t322 : ((-547492623481/10000000000000 : ℚ) : ℝ) ≤ stT267 322 := by
  have hc : ((-982439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547492623481/10000000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-982439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c323 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-526883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5314313/10000000) (δ := 2687/200000000) (ψ := -904683/1000000) 267 246
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t323 : ((-58638685039/2000000000000 : ℚ) : ℝ) ≤ stT267 323 := by
  have hc : ((-526933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58638685039/2000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-526933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c324 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((133569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3250937/10000000) (δ := 2687/200000000) (ψ := -904683/1000000) 267 246
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t324 : ((1854775923/125000000000 : ℚ) : ℝ) ≤ stT267 324 := by
  have hc : ((16693/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1854775923/125000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((16693/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c325 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((444053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1193969/10000000) (δ := 2687/200000000) (ψ := -904683/1000000) 267 246
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t325 : ((615755829/12500000000 : ℚ) : ℝ) ≤ stT267 325 := by
  have hc : ((111007/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((615755829/12500000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((111007/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c326 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((470927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34269/400000) (δ := 3367/250000000) (ψ := -904683/1000000) 267 246
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t326 : ((16300508181/312500000000 : ℚ) : ℝ) ≤ stT267 326 := by
  have hc : ((235451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16300508181/312500000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((235451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c327 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((9973/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 362643/1250000) (δ := 3367/250000000) (ψ := -904683/1000000) 267 246
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t327 : ((22057550887/1000000000000 : ℚ) : ℝ) ≤ stT267 327 := by
  have hc : ((39887/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22057550887/1000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((39887/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c328 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-393969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 987871/2000000) (δ := 1671/125000000) (ψ := -904683/1000000) 267 246
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t328 : ((-108780371501/5000000000000 : ℚ) : ℝ) ≤ stT267 328 := by
  have hc : ((-394019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108780371501/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-394019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c329 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-469157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1742823/2500000) (δ := 3367/250000000) (ψ := -904683/1000000) 267 246
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t329 : ((-64667120469/1250000000000 : ℚ) : ℝ) ≤ stT267 329 := by
  have hc : ((-234591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64667120469/1250000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-234591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c330 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-897273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1677719/2500000) (δ := 3357/250000000) (ψ := -904683/1000000) 267 247
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t330 : ((-246980079843/5000000000000 : ℚ) : ℝ) ≤ stT267 330 := by
  have hc : ((-897323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246980079843/5000000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-897323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c331 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-300953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4691221/10000000) (δ := 107/8000000) (ψ := -904683/1000000) 267 247
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t331 : ((-3308925979/200000000000 : ℚ) : ℝ) ≤ stT267 331 := by
  have hc : ((-301003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3308925979/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-301003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c332 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((479197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2677641/10000000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 247
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t332 : ((262965935687/10000000000000 : ℚ) : ℝ) ≤ stT267 332 := by
  have hc : ((479147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262965935687/10000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((479147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c333 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((15067/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335067/5000000) (δ := 539/40000000) (ψ := -904683/1000000) 267 247
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t333 : ((66049820881/1250000000000 : ℚ) : ℝ) ≤ stT267 333 := by
  have hc : ((482119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66049820881/1250000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((482119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c334 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((861517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332841/2500000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 247
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t334 : ((18854928229/400000000000 : ℚ) : ℝ) ≤ stT267 334 := by
  have hc : ((861467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18854928229/400000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((861467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c335 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((237729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1663461/5000000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 247
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t335 : ((64928911541/5000000000000 : ℚ) : ℝ) ≤ stT267 335 := by
  have hc : ((237679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64928911541/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((237679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c336 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-527617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5316473/10000000) (δ := 107/8000000) (ψ := -904683/1000000) 267 247
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t336 : ((-57573218703/2000000000000 : ℚ) : ℝ) ≤ stT267 336 := by
  have hc : ((-527667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57573218703/2000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-527667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c337 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-487781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7300149/10000000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 247
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t337 : ((-26572500141/500000000000 : ℚ) : ℝ) ≤ stT267 337 := by
  have hc : ((-243903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26572500141/500000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-243903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c338 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-421069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3215039/5000000) (δ := 6691/500000000) (ψ := -904683/1000000) 267 248
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t338 : ((-114522619163/2500000000000 : ℚ) : ℝ) ≤ stT267 338 := by
  have hc : ((-210547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114522619163/2500000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-210547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c339 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-210843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4458083/10000000) (δ := 13421/1000000000) (ψ := -904683/1000000) 267 248
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t339 : ((-57270735759/5000000000000 : ℚ) : ℝ) ≤ stT267 339 := by
  have hc : ((-210893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57270735759/5000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-210893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c340 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((108601/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1245981/5000000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 248
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t340 : ((29445861333/1000000000000 : ℚ) : ℝ) ≤ stT267 340 := by
  have hc : ((108591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29445861333/1000000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((108591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c341 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((977473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8307/156250) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 248
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t341 : ((52930387719/1000000000000 : ℚ) : ℝ) ≤ stT267 341 := by
  have hc : ((977423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52930387719/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((977423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c342 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((421167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1422993/10000000) (δ := 6741/500000000) (ψ := -904683/1000000) 267 248
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t342 : ((56931870699/1250000000000 : ℚ) : ℝ) ≤ stT267 342 := by
  have hc : ((210571/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56931870699/1250000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((210571/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c343 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((11011/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 842973/2500000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 248
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t343 : ((11888057133/1000000000000 : ℚ) : ℝ) ≤ stT267 343 := by
  have hc : ((22017/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11888057133/1000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((22017/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c344 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-527157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2657559/5000000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 248
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t344 : ((-71062758737/2500000000000 : ℚ) : ℝ) ≤ stT267 344 := by
  have hc : ((-527207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71062758737/2500000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-527207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c345 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-48561/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7252737/10000000) (δ := 13521/1000000000) (ψ := -904683/1000000) 267 248
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t345 : ((-26145714257/500000000000 : ℚ) : ℝ) ≤ stT267 345 := by
  have hc : ((-97127/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26145714257/500000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-97127/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c346 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-215413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6523281/10000000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 249
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t346 : ((-57906805251/1250000000000 : ℚ) : ℝ) ≤ stT267 346 := by
  have hc : ((-430851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57906805251/1250000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-430851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c347 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-264759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1149219/2500000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 249
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t347 : ((-142157150661/10000000000000 : ℚ) : ℝ) ≤ stT267 347 := by
  have hc : ((-264809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142157150661/10000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-264809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c348 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((479769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2676011/10000000) (δ := 6707/500000000) (ψ := -904683/1000000) 267 249
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t348 : ((32144531033/1250000000000 : ℚ) : ℝ) ≤ stT267 348 := by
  have hc : ((479719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32144531033/1250000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((479719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c349 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((954073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38031/500000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 249
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t349 : ((510676109601/10000000000000 : ℚ) : ℝ) ≤ stT267 349 := by
  have hc : ((954023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((510676109601/10000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((954023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c350 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((896189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1149231/10000000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 249
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t350 : ((239503005279/5000000000000 : ℚ) : ℝ) ≤ stT267 350 := by
  have hc : ((896139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239503005279/5000000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((896139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c351 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((68453/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 763419/2500000) (δ := 13489/1000000000) (ψ := -904683/1000000) 267 249
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t351 : ((28540731/1562500000 : ℚ) : ℝ) ≤ stT267 351 := by
  have hc : ((68443/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28540731/1562500000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((68443/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c352 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-7977/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2476323/5000000) (δ := 6757/500000000) (ψ := -904683/1000000) 267 249
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t352 : ((-1063072489/50000000000 : ℚ) : ℝ) ≤ stT267 352 := by
  have hc : ((-3989/10000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1063072489/50000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-3989/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c353 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-57491/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6846277/10000000) (δ := 6707/500000000) (ψ := -904683/1000000) 267 249
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t353 : ((-244808604391/5000000000000 : ℚ) : ℝ) ≤ stT267 353 := by
  have hc : ((-459953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244808604391/5000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-459953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c354 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-234651/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1394679/2000000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 250
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t354 : ((-49888990773/1000000000000 : ℚ) : ℝ) ≤ stT267 354 := by
  have hc : ((-469327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49888990773/1000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-469327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c355 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-112197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5090511/10000000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 250
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t355 : ((-23821852431/1000000000000 : ℚ) : ℝ) ≤ stT267 355 := by
  have hc : ((-224419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23821852431/1000000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-224419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c356 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((281793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1606417/5000000) (δ := 13407/1000000000) (ψ := -904683/1000000) 267 250
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t356 : ((74661613257/5000000000000 : ℚ) : ℝ) ≤ stT267 356 := by
  have hc : ((281743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74661613257/5000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((281743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c357 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((859657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83781/625000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 250
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t357 : ((56869020299/1250000000000 : ℚ) : ℝ) ≤ stT267 357 := by
  have hc : ((859607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56869020299/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((859607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c358 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((488947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 105327/2000000) (δ := 1687/125000000) (ψ := -904683/1000000) 267 250
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t358 : ((32300387469/625000000000 : ℚ) : ℝ) ≤ stT267 358 := by
  have hc : ((244461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32300387469/625000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((244461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c359 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((577263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2388559/10000000) (δ := 13407/1000000000) (ψ := -904683/1000000) 267 250
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t359 : ((304640899927/10000000000000 : ℚ) : ℝ) ≤ stT267 359 := by
  have hc : ((577213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304640899927/10000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((577213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c360 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-126997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132667/312500) (δ := 3349/250000000) (ψ := -904683/1000000) 267 250
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t360 : ((-66959740209/10000000000000 : ℚ) : ℝ) ≤ stT267 360 := by
  have hc : ((-127047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66959740209/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-127047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c361 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-38151/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3048461/5000000) (δ := 13407/1000000000) (ψ := -904683/1000000) 267 250
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t361 : ((-10040398753/250000000000 : ℚ) : ℝ) ≤ stT267 361 := by
  have hc : ((-76307/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10040398753/250000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-76307/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c362 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-3123/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -970567/1250000) (δ := 13399/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t362 : ((-52527890249/1000000000000 : ℚ) : ℝ) ≤ stT267 362 := by
  have hc : ((-99941/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52527890249/1000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-99941/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c363 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-71629/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -592317/1000000) (δ := 211/15625000) (ψ := -904683/1000000) 267 251
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t363 : ((-293735217/7812500000 : ℚ) : ℝ) ≤ stT267 363 := by
  have hc : ((-35817/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293735217/7812500000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-35817/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c364 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-63911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2043439/5000000) (δ := 13399/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t364 : ((-33524710423/10000000000000 : ℚ) : ℝ) ≤ stT267 364 := by
  have hc : ((-63961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33524710423/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-63961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c365 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((38741/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281949/1250000) (δ := 13499/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t365 : ((162210357969/5000000000000 : ℚ) : ℝ) ≤ stT267 365 := by
  have hc : ((309903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162210357969/5000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((309903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c366 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((985291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3354/78125) (δ := 13499/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t366 : ((128748338157/2500000000000 : ℚ) : ℝ) ≤ stT267 366 := by
  have hc : ((985241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128748338157/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((985241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c367 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((848959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 695981/5000000) (δ := 13399/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t367 : ((88625250691/2000000000000 : ℚ) : ℝ) ≤ stT267 367 := by
  have hc : ((848909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88625250691/2000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((848909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c368 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((56707/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 401037/1250000) (δ := 13499/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t368 : ((14777676171/1000000000000 : ℚ) : ℝ) ≤ stT267 368 := by
  have hc : ((56697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14777676171/1000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((56697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c369 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-6614/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5019691/10000000) (δ := 13399/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t369 : ((-5509636517/250000000000 : ℚ) : ℝ) ≤ stT267 369 := by
  have hc : ((-211673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5509636517/250000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-211673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c370 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-916679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6826213/10000000) (δ := 13399/1000000000) (ψ := -904683/1000000) 267 251
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t370 : ((-119146351401/2500000000000 : ℚ) : ℝ) ≤ stT267 370 := by
  have hc : ((-916729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119146351401/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-916729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c371 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-476239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -885021/1250000) (δ := 3373/250000000) (ψ := -904683/1000000) 267 252
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t371 : ((-1236321811/25000000000 : ℚ) : ℝ) ≤ stT267 371 := by
  have hc : ((-59533/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1236321811/25000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-59533/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c372 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-51633/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5283391/10000000) (δ := 13411/1000000000) (ψ := -904683/1000000) 267 252
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t372 : ((-3346632961/125000000000 : ℚ) : ℝ) ≤ stT267 372 := by
  have hc : ((-25819/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3346632961/125000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-25819/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c373 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((43337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3491421/10000000) (δ := 3373/250000000) (ψ := -904683/1000000) 267 252
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t373 : ((2243255961/250000000000 : ℚ) : ℝ) ≤ stT267 373 := by
  have hc : ((86649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2243255961/250000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((86649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c374 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((194121/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1704323/10000000) (δ := 837/62500000) (ψ := -904683/1000000) 267 252
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t374 : ((200741963879/5000000000000 : ℚ) : ℝ) ≤ stT267 374 := by
  have hc : ((388217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200741963879/5000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((388217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c375 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((124939/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39051/5000000) (δ := 3373/250000000) (ψ := -904683/1000000) 267 252
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t375 : ((258059589207/5000000000000 : ℚ) : ℝ) ≤ stT267 375 := by
  have hc : ((499731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258059589207/5000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((499731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c376 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((736923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927861/5000000) (δ := 13511/1000000000) (ψ := -904683/1000000) 267 252
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t376 : ((38001277483/1000000000000 : ℚ) : ℝ) ≤ stT267 376 := by
  have hc : ((736873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38001277483/1000000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((736873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c377 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((3721/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1814301/5000000) (δ := 13511/1000000000) (ψ := -904683/1000000) 267 252
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t377 : ((15324856143/2500000000000 : ℚ) : ℝ) ≤ stT267 377 := by
  have hc : ((59511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15324856143/2500000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((59511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c378 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-277319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5396809/10000000) (δ := 837/62500000) (ψ := -904683/1000000) 267 252
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t378 : ((-891565623/31250000000 : ℚ) : ℝ) ≤ stT267 378 := by
  have hc : ((-8667/15625 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-891565623/31250000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-8667/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c379 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-961763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7160411/10000000) (δ := 13411/1000000000) (ψ := -904683/1000000) 267 252
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t379 : ((-247025318229/5000000000000 : ℚ) : ℝ) ≤ stT267 379 := by
  have hc : ((-961813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247025318229/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-961813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c380 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-455289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -678869/1000000) (δ := 2677/200000000) (ψ := -904683/1000000) 267 253
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t380 : ((-11678576443/250000000000 : ℚ) : ℝ) ≤ stT267 380 := by
  have hc : ((-227657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11678576443/250000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-227657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c381 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-428631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5034433/10000000) (δ := 6709/500000000) (ψ := -904683/1000000) 267 253
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t381 : ((-54905033799/2500000000000 : ℚ) : ℝ) ≤ stT267 381 := by
  have hc : ((-428681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54905033799/2500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-428681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c382 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((127047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656943/2000000) (δ := 6759/500000000) (ψ := -904683/1000000) 267 253
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t382 : ((8123755521/625000000000 : ℚ) : ℝ) ≤ stT267 382 := by
  have hc : ((63511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8123755521/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((63511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c383 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((51017/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153967/1000000) (δ := 6709/500000000) (ψ := -904683/1000000) 267 253
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t383 : ((203647389/4882812500 : ℚ) : ℝ) ≤ stT267 383 := by
  have hc : ((408111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203647389/4882812500 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((408111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c384 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((996773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200903/10000000) (δ := 6709/500000000) (ψ := -904683/1000000) 267 253
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t384 : ((50863771413/1000000000000 : ℚ) : ℝ) ≤ stT267 384 := by
  have hc : ((996723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50863771413/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((996723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c385 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((714579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1936937/10000000) (δ := 6709/500000000) (ψ := -904683/1000000) 267 253
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t385 : ((364157561263/10000000000000 : ℚ) : ℝ) ≤ stT267 385 := by
  have hc : ((714529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364157561263/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((714529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c386 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((103239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229277/625000) (δ := 6709/500000000) (ψ := -904683/1000000) 267 253
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t386 : ((26260878177/5000000000000 : ℚ) : ℝ) ≤ stT267 386 := by
  have hc : ((103189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26260878177/5000000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((103189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c387 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-554187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1079091/2000000) (δ := 6759/500000000) (ψ := -904683/1000000) 267 253
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t387 : ((-281734739973/10000000000000 : ℚ) : ℝ) ≤ stT267 387 := by
  have hc : ((-554237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281734739973/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-554237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c388 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-956987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 889759/1250000) (δ := 6709/500000000) (ψ := -904683/1000000) 267 253
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t388 : ((-242931400969/5000000000000 : ℚ) : ℝ) ≤ stT267 388 := by
  have hc : ((-957037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242931400969/5000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-957037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c389 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-184761/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3435873/5000000) (δ := 541/40000000) (ψ := -904683/1000000) 267 254
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t389 : ((-93682777191/2000000000000 : ℚ) : ℝ) ≤ stT267 389 := by
  have hc : ((-184771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93682777191/2000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-184771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c390 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-118187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5158007/10000000) (δ := 6689/500000000) (ψ := -904683/1000000) 267 254
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t390 : ((-11970536163/500000000000 : ℚ) : ℝ) ≤ stT267 390 := by
  have hc : ((-236399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11970536163/500000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-236399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c391 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((95081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3448673/10000000) (δ := 6689/500000000) (ψ := -904683/1000000) 267 254
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t391 : ((3004488461/312500000000 : ℚ) : ℝ) ≤ stT267 391 := by
  have hc : ((5941/31250 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3004488461/312500000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((5941/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c392 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((766469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -871839/5000000) (δ := 6739/500000000) (ψ := -904683/1000000) 267 254
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t392 : ((96774960711/2500000000000 : ℚ) : ℝ) ≤ stT267 392 := by
  have hc : ((766419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96774960711/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((766419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c393 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((249963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43021/10000000) (δ := 537/40000000) (ψ := -904683/1000000) 267 254
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t393 : ((252166561133/5000000000000 : ℚ) : ℝ) ≤ stT267 393 := by
  have hc : ((499901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252166561133/5000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((499901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c394 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((789183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1653297/10000000) (δ := 541/40000000) (ψ := -904683/1000000) 267 254
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t394 : ((24847430771/625000000000 : ℚ) : ℝ) ≤ stT267 394 := by
  have hc : ((789133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24847430771/625000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((789133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c395 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((3603/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 836319/2500000) (δ := 541/40000000) (ψ := -904683/1000000) 267 254
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t395 : ((28999532367/2500000000000 : ℚ) : ℝ) ≤ stT267 395 := by
  have hc : ((115271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28999532367/2500000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((115271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c396 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-428131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5033049/10000000) (δ := 6739/500000000) (ψ := -904683/1000000) 267 254
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t396 : ((-215169087939/10000000000000 : ℚ) : ℝ) ≤ stT267 396 := by
  have hc : ((-428181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215169087939/10000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-428181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c397 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-898261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1679121/2500000) (δ := 6739/500000000) (ψ := -904683/1000000) 267 254
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t397 : ((-225424857273/5000000000000 : ℚ) : ℝ) ≤ stT267 397 := by
  have hc : ((-898311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225424857273/5000000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-898311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c398 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-30519/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3656091/5000000) (δ := 3383/250000000) (ψ := -904683/1000000) 267 255
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t398 : ((-48955470579/1000000000000 : ℚ) : ℝ) ≤ stT267 398 := by
  have hc : ((-488329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48955470579/1000000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-488329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c399 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-12639/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2818579/5000000) (δ := 13371/1000000000) (ψ := -904683/1000000) 267 255
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t399 : ((-39549533/1250000000 : ℚ) : ℝ) ≤ stT267 399 := by
  have hc : ((-79/125 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39549533/1250000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-79/125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c400 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-15739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3966339/10000000) (δ := 13471/1000000000) (ψ := -904683/1000000) 267 255
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t400 : ((-7894515789/10000000000000 : ℚ) : ℝ) ≤ stT267 400 := by
  have hc : ((-15789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7894515789/10000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-15789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c401 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((605929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1149829/5000000) (δ := 13371/1000000000) (ψ := -904683/1000000) 267 255
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t401 : ((18910089469/625000000000 : ℚ) : ℝ) ≤ stT267 401 := by
  have hc : ((605879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18910089469/625000000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((605879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c402 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((193539/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -318591/5000000) (δ := 3383/250000000) (ψ := -904683/1000000) 267 255
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t402 : ((48261681433/1000000000000 : ℚ) : ℝ) ≤ stT267 402 := by
  have hc : ((193529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48261681433/1000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((193529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c403 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((458861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021221/10000000) (δ := 13471/1000000000) (ψ := -904683/1000000) 267 255
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t403 : ((11428113543/250000000000 : ℚ) : ℝ) ≤ stT267 403 := by
  have hc : ((114709/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11428113543/250000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((114709/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c404 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((479953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2675487/10000000) (δ := 3383/250000000) (ψ := -904683/1000000) 267 255
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t404 : ((119380190377/5000000000000 : ℚ) : ℝ) ≤ stT267 404 := by
  have hc : ((479903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119380190377/5000000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((479903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c405 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-158801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54071/125000) (δ := 13371/1000000000) (ψ := -904683/1000000) 267 255
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t405 : ((-9866712163/1250000000000 : ℚ) : ℝ) ≤ stT267 405 := by
  have hc : ((-158851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9866712163/1250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-158851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c406 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-11402/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2985901/5000000) (δ := 1679/125000000) (ψ := -904683/1000000) 267 255
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t406 : ((-45272872897/1250000000000 : ℚ) : ℝ) ≤ stT267 406 := by
  have hc : ((-364889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45272872897/1250000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-364889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c407 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-995391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1903463/2500000) (δ := 1679/125000000) (ψ := -904683/1000000) 267 255
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t407 : ((-246711092881/5000000000000 : ℚ) : ℝ) ≤ stT267 407 := by
  have hc : ((-995441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246711092881/5000000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-995441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c408 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-423849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3228033/5000000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 256
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t408 : ((-52462249169/1250000000000 : ℚ) : ℝ) ≤ stT267 408 := by
  have hc : ((-211937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52462249169/1250000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-211937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c409 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-70083/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2411013/5000000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 256
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t409 : ((-34658815617/2000000000000 : ℚ) : ℝ) ≤ stT267 409 := by
  have hc : ((-70093/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34658815617/2000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-70093/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c410 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((289783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3191991/10000000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 256
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t410 : ((17886087289/1250000000000 : ℚ) : ℝ) ≤ stT267 410 := by
  have hc : ((289733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17886087289/1250000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((289733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c411 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((101271/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313179/2000000) (δ := 1683/125000000) (ψ := -904683/1000000) 267 256
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t411 : ((199800617517/5000000000000 : ℚ) : ℝ) ≤ stT267 411 := by
  have hc : ((405059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199800617517/5000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((405059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c412 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((999747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56197/10000000) (δ := 3341/250000000) (ψ := -904683/1000000) 267 256
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t412 : ((61564340351/1250000000000 : ℚ) : ℝ) ≤ stT267 412 := by
  have hc : ((999697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61564340351/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((999697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c413 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((783983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1674351/10000000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 256
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t413 : ((385747559511/10000000000000 : ℚ) : ℝ) ≤ stT267 413 := by
  have hc : ((783933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((385747559511/10000000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((783933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c414 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((252577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3288633/10000000) (δ := 13539/1000000000) (ψ := -904683/1000000) 267 256
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t414 : ((124110202271/10000000000000 : ℚ) : ℝ) ≤ stT267 414 := by
  have hc : ((252527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124110202271/10000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((252527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c415 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-189549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4899043/10000000) (δ := 3341/250000000) (ψ := -904683/1000000) 267 256
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t415 : ((-46529137347/2500000000000 : ℚ) : ℝ) ≤ stT267 415 := by
  have hc : ((-94787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46529137347/2500000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-94787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c416 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-107253/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1301103/2000000) (δ := 1683/125000000) (ψ := -904683/1000000) 267 256
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t416 : ((-210352979767/5000000000000 : ℚ) : ℝ) ≤ stT267 416 := by
  have hc : ((-429037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210352979767/5000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-429037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c417 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-198967/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -379989/500000) (δ := 13547/1000000000) (ψ := -904683/1000000) 267 257
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t417 : ((-97439633831/2000000000000 : ℚ) : ℝ) ≤ stT267 417 := by
  have hc : ((-198977/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97439633831/2000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-198977/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c418 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-36883/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -750123/1250000) (δ := 13547/1000000000) (ψ := -904683/1000000) 267 257
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t418 : ((-9020644109/250000000000 : ℚ) : ℝ) ≤ stT267 418 := by
  have hc : ((-73771/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9020644109/250000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-73771/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c419 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-190431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4405993/10000000) (δ := 13447/1000000000) (ψ := -904683/1000000) 267 257
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t419 : ((-23264015973/2500000000000 : ℚ) : ℝ) ≤ stT267 419 := by
  have hc : ((-190481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23264015973/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-190481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c420 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((53793/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2814807/10000000) (δ := 841/62500000) (ψ := -904683/1000000) 267 257
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t420 : ((2099619573/100000000000 : ℚ) : ℝ) ≤ stT267 420 := by
  have hc : ((215147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2099619573/100000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((215147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c421 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((220469/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -49097/400000) (δ := 3339/250000000) (ψ := -904683/1000000) 267 257
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t421 : ((21488776881/500000000000 : ℚ) : ℝ) ≤ stT267 421 := by
  have hc : ((440913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21488776881/500000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((440913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c422 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((494933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 356219/10000000) (δ := 13447/1000000000) (ψ := -904683/1000000) 267 257
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t422 : ((7528664223/156250000000 : ℚ) : ℝ) ≤ stT267 422 := by
  have hc : ((123727/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7528664223/156250000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((123727/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c423 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((28593/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 968029/5000000) (δ := 13447/1000000000) (ψ := -904683/1000000) 267 257
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t423 : ((1737675207/50000000000 : ℚ) : ℝ) ≤ stT267 423 := by
  have hc : ((28591/40000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1737675207/50000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((28591/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c424 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((82573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1756113/5000000) (δ := 13547/1000000000) (ψ := -904683/1000000) 267 257
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t424 : ((5011096977/625000000000 : ℚ) : ℝ) ≤ stT267 424 := by
  have hc : ((20637/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5011096977/625000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((20637/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c425 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-446693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1016931/2000000) (δ := 841/62500000) (ψ := -904683/1000000) 267 257
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t425 : ((-13543907531/625000000000 : ℚ) : ℝ) ≤ stT267 425 := by
  have hc : ((-446743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13543907531/625000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-446743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c426 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-88689/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3326707/5000000) (δ := 13447/1000000000) (ψ := -904683/1000000) 267 257
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t426 : ((-10743105097/250000000000 : ℚ) : ℝ) ≤ stT267 426 := by
  have hc : ((-44347/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10743105097/250000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-44347/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c427 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-989389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3744731/5000000) (δ := 6727/500000000) (ψ := -904683/1000000) 267 258
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t427 : ((-239411586513/5000000000000 : ℚ) : ℝ) ≤ stT267 427 := by
  have hc : ((-989439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239411586513/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-989439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c428 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-717669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5928113/10000000) (δ := 6677/500000000) (ψ := -904683/1000000) 267 258
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t428 : ((-346923115311/10000000000000 : ℚ) : ℝ) ≤ stT267 428 := by
  have hc : ((-717719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346923115311/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-717719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c429 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-176397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2185151/5000000) (δ := 13549/1000000000) (ψ := -904683/1000000) 267 258
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t429 : ((-17037898767/2000000000000 : ℚ) : ℝ) ≤ stT267 429 := by
  have hc : ((-176447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17037898767/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-176447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c430 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((85971/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2816161/10000000) (δ := 6727/500000000) (ψ := -904683/1000000) 267 258
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t430 : ((20727002281/1000000000000 : ℚ) : ℝ) ≤ stT267 430 := by
  have hc : ((85961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20727002281/1000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((85961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c431 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((218639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316423/2500000) (δ := 6727/500000000) (ψ := -904683/1000000) 267 258
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t431 : ((210617336799/5000000000000 : ℚ) : ℝ) ≤ stT267 431 := by
  have hc : ((437253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210617336799/5000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((437253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c432 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((993679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281239/10000000) (δ := 6677/500000000) (ψ := -904683/1000000) 267 258
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t432 : ((3824478021/80000000000 : ℚ) : ℝ) ≤ stT267 432 := by
  have hc : ((993629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3824478021/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((993629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c433 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((745273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228079/1250000) (δ := 13549/1000000000) (ψ := -904683/1000000) 267 258
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t433 : ((358131071887/10000000000000 : ℚ) : ℝ) ≤ stT267 433 := by
  have hc : ((745223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358131071887/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((745223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c434 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((111567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3364421/10000000) (δ := 13549/1000000000) (ψ := -904683/1000000) 267 258
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t434 : ((5354183313/500000000000 : ℚ) : ℝ) ≤ stT267 434 := by
  have hc : ((55771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5354183313/500000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((55771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c435 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-379701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4900673/10000000) (δ := 6727/500000000) (ψ := -904683/1000000) 267 258
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t435 : ((-22759616683/1250000000000 : ℚ) : ℝ) ≤ stT267 435 := by
  have hc : ((-379751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22759616683/1250000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-379751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c436 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-16857/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3216693/5000000) (δ := 13449/1000000000) (ψ := -904683/1000000) 267 258
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t436 : ((-2018383053/50000000000 : ℚ) : ℝ) ≤ stT267 436 := by
  have hc : ((-8429/10000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2018383053/50000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-8429/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c437 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-999057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7745401/10000000) (δ := 13461/1000000000) (ψ := -904683/1000000) 267 259
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t437 : ((-95587564011/2000000000000 : ℚ) : ℝ) ≤ stT267 437 := by
  have hc : ((-999107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95587564011/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-999107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c438 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-396907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -621963/1000000) (δ := 6721/500000000) (ψ := -904683/1000000) 267 259
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t438 : ((-47415412827/1250000000000 : ℚ) : ℝ) ≤ stT267 438 := by
  have hc : ((-99233/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47415412827/1250000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-99233/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c439 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-75827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1174349/2500000) (δ := 13361/1000000000) (ψ := -904683/1000000) 267 259
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t439 : ((-36196221523/2500000000000 : ℚ) : ℝ) ≤ stT267 439 := by
  have hc : ((-151679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36196221523/2500000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-151679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c440 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((294893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3178633/10000000) (δ := 13461/1000000000) (ψ := -904683/1000000) 267 259
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t440 : ((140560798233/10000000000000 : ℚ) : ℝ) ≤ stT267 440 := by
  have hc : ((294843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140560798233/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((294843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c441 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((786709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -831671/5000000) (δ := 6771/500000000) (ψ := -904683/1000000) 267 259
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t441 : ((37459914921/1000000000000 : ℚ) : ℝ) ≤ stT267 441 := by
  have hc : ((786659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37459914921/1000000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((786659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c442 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((199633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75727/5000000) (δ := 13361/1000000000) (ψ := -904683/1000000) 267 259
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t442 : ((94950879573/2000000000000 : ℚ) : ℝ) ≤ stT267 442 := by
  have hc : ((199623/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94950879573/2000000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((199623/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c443 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((42813/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1357029/10000000) (δ := 6721/500000000) (ψ := -904683/1000000) 267 259
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t443 : ((20339867897/500000000000 : ℚ) : ℝ) ≤ stT267 443 := by
  have hc : ((85621/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20339867897/500000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((85621/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c444 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((413189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715527/2500000) (δ := 6721/500000000) (ψ := -904683/1000000) 267 259
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t444 : ((98033340171/5000000000000 : ℚ) : ℝ) ≤ stT267 444 := by
  have hc : ((413139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98033340171/5000000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((413139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c445 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-173829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4363783/10000000) (δ := 13361/1000000000) (ψ := -904683/1000000) 267 259
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t445 : ((-41213322217/5000000000000 : ℚ) : ℝ) ≤ stT267 445 := by
  have hc : ((-173879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41213322217/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-173879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c446 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-349519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146553/250000) (δ := 6721/500000000) (ψ := -904683/1000000) 267 259
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t446 : ((-10344623601/312500000000 : ℚ) : ℝ) ≤ stT267 446 := by
  have hc : ((-43693/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10344623601/312500000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-43693/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c447 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-98031/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7357053/10000000) (δ := 6721/500000000) (ψ := -904683/1000000) 267 259
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t447 : ((-1449045607/31250000000 : ℚ) : ℝ) ≤ stT267 447 := by
  have hc : ((-24509/25000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1449045607/31250000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-24509/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c448 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-921879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -428703/625000) (δ := 2687/200000000) (ψ := -904683/1000000) 267 260
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t448 : ((-54446360953/1250000000000 : ℚ) : ℝ) ≤ stT267 448 := by
  have hc : ((-921929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54446360953/1250000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-921929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c449 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-109203/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -537099/1000000) (δ := 2687/200000000) (ψ := -904683/1000000) 267 260
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t449 : ((-5154089109/200000000000 : ℚ) : ℝ) ≤ stT267 449 := by
  have hc : ((-109213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5154089109/200000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-109213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c450 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((8197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3886003/10000000) (δ := 2707/200000000) (ψ := -904683/1000000) 267 260
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t450 : ((240769593/312500000000 : ℚ) : ℝ) ≤ stT267 450 := by
  have hc : ((2043/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240769593/312500000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((2043/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c451 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((114423/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1202143/5000000) (δ := 1671/125000000) (ψ := -904683/1000000) 267 260
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t451 : ((53874907853/2000000000000 : ℚ) : ℝ) ≤ stT267 451 := by
  have hc : ((114413/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53874907853/2000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((114413/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c452 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((233049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -925907/10000000) (δ := 1671/125000000) (ψ := -904683/1000000) 267 260
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t452 : ((5480552407/125000000000 : ℚ) : ℝ) ≤ stT267 452 := by
  have hc : ((466073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5480552407/125000000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((466073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c453 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((975961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137317/2500000) (δ := 1671/125000000) (ψ := -904683/1000000) 267 260
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t453 : ((5731525303/125000000000 : ℚ) : ℝ) ≤ stT267 453 := by
  have hc : ((975911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5731525303/125000000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((975911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c454 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((345313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404221/2000000) (δ := 2707/200000000) (ψ := -904683/1000000) 267 260
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t454 : ((20256450003/625000000000 : ℚ) : ℝ) ≤ stT267 454 := by
  have hc : ((43161/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20256450003/625000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((43161/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c455 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((5437/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1744903/5000000) (δ := 3367/250000000) (ψ := -904683/1000000) 267 260
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t455 : ((40770738369/5000000000000 : ℚ) : ℝ) ≤ stT267 455 := by
  have hc : ((86967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40770738369/5000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((86967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c456 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-399799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 991047/2000000) (δ := 2687/200000000) (ψ := -904683/1000000) 267 260
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t456 : ((-187246487757/10000000000000 : ℚ) : ℝ) ≤ stT267 456 := by
  have hc : ((-399849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187246487757/10000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-399849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c457 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-839391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3208697/5000000) (δ := 1671/125000000) (ψ := -904683/1000000) 267 260
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t457 : ((-392674550421/10000000000000 : ℚ) : ℝ) ≤ stT267 457 := by
  have hc : ((-839441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-392674550421/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-839441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c458 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-24999/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957887/2500000) (δ := 3357/250000000) (ψ := -904683/1000000) 267 261
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t458 : ((-4672746727/100000000000 : ℚ) : ℝ) ≤ stT267 458 := by
  have hc : ((-100001/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4672746727/100000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-100001/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c459 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-415101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -398479/625000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 261
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t459 : ((-96882313443/2500000000000 : ℚ) : ℝ) ≤ stT267 459 := by
  have hc : ((-207563/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96882313443/2500000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-207563/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c460 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-193983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98461/200000) (δ := 107/8000000) (ψ := -904683/1000000) 267 261
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t460 : ((-11307101503/625000000000 : ℚ) : ℝ) ≤ stT267 460 := by
  have hc : ((-24251/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11307101503/625000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-24251/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c461 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((451/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3473507/10000000) (δ := 107/8000000) (ψ := -904683/1000000) 267 261
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t461 : ((839972911/100000000000 : ℚ) : ℝ) ≤ stT267 461 := by
  have hc : ((3607/20000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((839972911/100000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((3607/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c462 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((68887/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63349/312500) (δ := 107/8000000) (ψ := -904683/1000000) 267 261
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t462 : ((8011699861/250000000000 : ℚ) : ℝ) ≤ stT267 462 := by
  have hc : ((34441/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8011699861/250000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((34441/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c463 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((972849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5839/100000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 261
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t463 : ((452097634461/10000000000000 : ℚ) : ℝ) ≤ stT267 463 := by
  have hc : ((972799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452097634461/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((972799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c464 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((5887/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107029/1250000) (δ := 539/40000000) (ψ := -904683/1000000) 267 261
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t464 : ((21862592253/500000000000 : ℚ) : ℝ) ≤ stT267 464 := by
  have hc : ((94187/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21862592253/500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((94187/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c465 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((607953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 573323/2500000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 261
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t465 : ((140953860707/5000000000000 : ℚ) : ℝ) ≤ stT267 465 := by
  have hc : ((607903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140953860707/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((607903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c466 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((3193/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 232951/625000) (δ := 107/8000000) (ψ := -904683/1000000) 267 261
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t466 : ((1478202031/400000000000 : ℚ) : ℝ) ≤ stT267 466 := by
  have hc : ((3191/40000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1478202031/400000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((3191/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c467 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-47277/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5158069/10000000) (δ := 107/8000000) (ψ := -904683/1000000) 267 261
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t467 : ((-2187950909/100000000000 : ℚ) : ℝ) ≤ stT267 467 := by
  have hc : ((-23641/50000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2187950909/100000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-23641/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c468 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-874083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6585851/10000000) (δ := 1691/125000000) (ψ := -904683/1000000) 267 261
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t468 : ((-404068853383/10000000000000 : ℚ) : ℝ) ≤ stT267 468 := by
  have hc : ((-874133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404068853383/10000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-874133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c469 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-499019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7697333/10000000) (δ := 13383/1000000000) (ψ := -904683/1000000) 267 262
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t469 : ((-28804694919/625000000000 : ℚ) : ℝ) ≤ stT267 469 := by
  have hc : ((-124761/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28804694919/625000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-124761/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c470 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-201809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10041/16000) (δ := 671/50000000) (ψ := -904683/1000000) 267 262
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t470 : ((-93093396019/2500000000000 : ℚ) : ℝ) ≤ stT267 470 := by
  have hc : ((-403643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93093396019/2500000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-403643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c471 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-363453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121423/250000) (δ := 13483/1000000000) (ψ := -904683/1000000) 267 262
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t471 : ((-20936682291/1250000000000 : ℚ) : ℝ) ≤ stT267 471 := by
  have hc : ((-363503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20936682291/1250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-363503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c472 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((3017/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172061/500000) (δ := 169/12500000) (ψ := -904683/1000000) 267 262
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t472 : ((44426440953/5000000000000 : ℚ) : ℝ) ≤ stT267 472 := by
  have hc : ((96519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44426440953/5000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((96519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c473 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((688477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2028523/10000000) (δ := 169/12500000) (ψ := -904683/1000000) 267 262
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t473 : ((1582693673/50000000000 : ℚ) : ℝ) ≤ stT267 473 := by
  have hc : ((688427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1582693673/50000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((688427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c474 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((969527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618763/10000000) (δ := 169/12500000) (ψ := -904683/1000000) 267 262
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t474 : ((89059065651/2000000000000 : ℚ) : ℝ) ≤ stT267 474 := by
  have hc : ((969477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89059065651/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((969477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c475 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((190147/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393997/5000000) (δ := 13483/1000000000) (ψ := -904683/1000000) 267 262
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t475 : ((87240749847/2000000000000 : ℚ) : ℝ) ≤ stT267 475 := by
  have hc : ((190137/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87240749847/2000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((190137/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c476 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((159923/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1095873/5000000) (δ := 671/50000000) (ψ := -904683/1000000) 267 262
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t476 : ((146589635529/5000000000000 : ℚ) : ℝ) ≤ stT267 476 := by
  have hc : ((319821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146589635529/5000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((319821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c477 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((133373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1796281/5000000) (δ := 13483/1000000000) (ψ := -904683/1000000) 267 262
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t477 : ((15261083841/2500000000000 : ℚ) : ℝ) ≤ stT267 477 := by
  have hc : ((133323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15261083841/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((133323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c478 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-412691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4990507/10000000) (δ := 13383/1000000000) (ψ := -904683/1000000) 267 262
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t478 : ((-18878360599/1000000000000 : ℚ) : ℝ) ≤ stT267 478 := by
  have hc : ((-412741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18878360599/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-412741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c479 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-832377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 798181/1250000) (δ := 169/12500000) (ψ := -904683/1000000) 267 262
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t479 : ((-23771617839/625000000000 : ℚ) : ℝ) ≤ stT267 479 := by
  have hc : ((-832427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23771617839/625000000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-832427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c480 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-999533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3888793/5000000) (δ := 169/12500000) (ψ := -904683/1000000) 267 262
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t480 : ((-114061416547/2500000000000 : ℚ) : ℝ) ≤ stT267 480 := by
  have hc : ((-999583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114061416547/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-999583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c481 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-216319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6541243/10000000) (δ := 13513/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t481 : ((-197277454143/5000000000000 : ℚ) : ℝ) ≤ stT267 481 := by
  have hc : ((-432663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197277454143/5000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-432663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c482 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-471657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161091/312500) (δ := 13413/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t482 : ((-3357138719/156250000000 : ℚ) : ℝ) ≤ stT267 482 := by
  have hc : ((-471707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3357138719/156250000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-471707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c483 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((62149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1885759/5000000) (δ := 1339/100000000) (ψ := -904683/1000000) 267 263
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t483 : ((5651195297/2000000000000 : ℚ) : ℝ) ≤ stT267 483 := by
  have hc : ((62099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5651195297/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((62099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c484 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((576489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149433/625000) (δ := 13413/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t484 : ((52403493051/2000000000000 : ℚ) : ℝ) ≤ stT267 484 := by
  have hc : ((576439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52403493051/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((576439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c485 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((45949/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40531/400000) (δ := 13513/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t485 : ((10431601467/250000000000 : ℚ) : ℝ) ≤ stT267 485 := by
  have hc : ((91893/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10431601467/250000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((91893/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c486 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((197911/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180821/5000000) (δ := 1339/100000000) (ψ := -904683/1000000) 267 263
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t486 : ((89769674709/2000000000000 : ℚ) : ℝ) ≤ stT267 486 := by
  have hc : ((197901/200000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89769674709/2000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((197901/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c487 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((769029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 216711/1250000) (δ := 13413/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t487 : ((348457450997/10000000000000 : ℚ) : ℝ) ≤ stT267 487 := by
  have hc : ((768979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348457450997/10000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((768979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c488 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((323687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3102931/10000000) (δ := 1339/100000000) (ψ := -904683/1000000) 267 263
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t488 : ((73251674943/5000000000000 : ℚ) : ℝ) ≤ stT267 488 := by
  have hc : ((323637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73251674943/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((323637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c489 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-53807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4469303/10000000) (δ := 13513/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t489 : ((-6084509753/625000000000 : ℚ) : ℝ) ≤ stT267 489 := by
  have hc : ((-107639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6084509753/625000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-107639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c490 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-172661/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5832939/10000000) (δ := 13413/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t490 : ((-78005944319/2500000000000 : ℚ) : ℝ) ≤ stT267 490 := by
  have hc : ((-345347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78005944319/2500000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-345347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c491 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-965339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3596919/5000000) (δ := 13413/1000000000) (ψ := -904683/1000000) 267 263
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t491 : ((-217837131683/5000000000000 : ℚ) : ℝ) ≤ stT267 491 := by
  have hc : ((-965389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217837131683/5000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-965389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c492 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-480641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -715603/1000000) (δ := 6753/500000000) (ψ := -904683/1000000) 267 264
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t492 : ((-21670105611/500000000000 : ℚ) : ℝ) ≤ stT267 492 := by
  have hc : ((-240333/250000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21670105611/500000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-240333/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c493 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-85159/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2900369/5000000) (δ := 6753/500000000) (ψ := -904683/1000000) 267 264
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t493 : ((-76713109929/2500000000000 : ℚ) : ℝ) ≤ stT267 493 := by
  have hc : ((-340661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76713109929/2500000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-340661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c494 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((-6467/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1112029/2500000) (δ := 6753/500000000) (ψ := -904683/1000000) 267 264
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t494 : ((-23282788617/2500000000000 : ℚ) : ℝ) ≤ stT267 494 := by
  have hc : ((-103497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23282788617/2500000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-103497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c495 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((1017/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3098297/10000000) (δ := 13397/1000000000) (ψ := -904683/1000000) 267 264
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t495 : ((7312587087/500000000000 : ℚ) : ℝ) ≤ stT267 495 := by
  have hc : ((32539/100000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7312587087/500000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((32539/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c496 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((382273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1751149/10000000) (δ := 6753/500000000) (ψ := -904683/1000000) 267 264
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t496 : ((21454290153/625000000000 : ℚ) : ℝ) ≤ stT267 496 := by
  have hc : ((47781/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21454290153/625000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((47781/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c497 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((493397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -406737/10000000) (δ := 6703/500000000) (ψ := -904683/1000000) 267 264
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t497 : ((55326859423/1250000000000 : ℚ) : ℝ) ≤ stT267 497 := by
  have hc : ((123343/125000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55326859423/1250000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((123343/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c498 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((465441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467469/5000000) (δ := 6703/500000000) (ψ := -904683/1000000) 267 264
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t498 : ((2606969547/62500000000 : ℚ) : ℝ) ≤ stT267 498 := by
  have hc : ((58177/62500 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2606969547/62500000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((58177/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c499 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((614079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2273943/10000000) (δ := 6703/500000000) (ψ := -904683/1000000) 267 264
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t499 : ((274876836169/10000000000000 : ℚ) : ℝ) ≤ stT267 499 := by
  have hc : ((614029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274876836169/10000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((614029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_c500 :
    |Real.cos (((267 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((126347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1805139/5000000) (δ := 6703/500000000) (ψ := -904683/1000000) 267 264
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st267_t500 : ((56481660261/10000000000000 : ℚ) : ℝ) ≤ stT267 500 := by
  have hc : ((126297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((267 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st267_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56481660261/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((126297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st267_p1 : ((123577/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT267 (i+1) := by
  rw [Finset.sum_range_one]
  exact st267_t1

theorem st267_p2 : ((1670465893/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT267 (i+1))
      = (∑ i ∈ Finset.range 1, stT267 (i+1)) + stT267 2 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 1
    simpa using h
  have hprev := st267_p1
  have hstep := st267_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p3 : ((1585583502247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT267 (i+1))
      = (∑ i ∈ Finset.range 2, stT267 (i+1)) + stT267 3 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 2
    simpa using h
  have hprev := st267_p2
  have hstep := st267_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p4 : ((3944553502247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT267 (i+1))
      = (∑ i ∈ Finset.range 3, stT267 (i+1)) + stT267 4 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 3
    simpa using h
  have hprev := st267_p3
  have hstep := st267_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p5 : ((1765447098479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT267 (i+1))
      = (∑ i ∈ Finset.range 4, stT267 (i+1)) + stT267 5 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 4
    simpa using h
  have hprev := st267_p4
  have hstep := st267_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p6 : ((106934582413/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT267 (i+1))
      = (∑ i ∈ Finset.range 5, stT267 (i+1)) + stT267 6 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 5
    simpa using h
  have hprev := st267_p5
  have hstep := st267_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p7 : ((4581003802141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT267 (i+1))
      = (∑ i ∈ Finset.range 6, stT267 (i+1)) + stT267 7 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 6
    simpa using h
  have hprev := st267_p6
  have hstep := st267_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p8 : ((1050384194401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT267 (i+1))
      = (∑ i ∈ Finset.range 7, stT267 (i+1)) + stT267 8 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 7
    simpa using h
  have hprev := st267_p7
  have hstep := st267_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p9 : ((-2270849803179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT267 (i+1))
      = (∑ i ∈ Finset.range 8, stT267 (i+1)) + stT267 9 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 8
    simpa using h
  have hprev := st267_p8
  have hstep := st267_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p10 : ((110760763871/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT267 (i+1))
      = (∑ i ∈ Finset.range 9, stT267 (i+1)) + stT267 10 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 9
    simpa using h
  have hprev := st267_p9
  have hstep := st267_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p11 : ((950349717667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT267 (i+1))
      = (∑ i ∈ Finset.range 10, stT267 (i+1)) + stT267 11 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 10
    simpa using h
  have hprev := st267_p10
  have hstep := st267_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p12 : ((898334055067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT267 (i+1))
      = (∑ i ∈ Finset.range 11, stT267 (i+1)) + stT267 12 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 11
    simpa using h
  have hprev := st267_p11
  have hstep := st267_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p13 : ((1340639354317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT267 (i+1))
      = (∑ i ∈ Finset.range 12, stT267 (i+1)) + stT267 13 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 12
    simpa using h
  have hprev := st267_p12
  have hstep := st267_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p14 : ((2356505449487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT267 (i+1))
      = (∑ i ∈ Finset.range 13, stT267 (i+1)) + stT267 14 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 13
    simpa using h
  have hprev := st267_p13
  have hstep := st267_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p15 : ((518277004973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT267 (i+1))
      = (∑ i ∈ Finset.range 14, stT267 (i+1)) + stT267 15 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 14
    simpa using h
  have hprev := st267_p14
  have hstep := st267_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p16 : ((761681754973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT267 (i+1))
      = (∑ i ∈ Finset.range 15, stT267 (i+1)) + stT267 16 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 15
    simpa using h
  have hprev := st267_p15
  have hstep := st267_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p17 : ((1316507644013/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT267 (i+1))
      = (∑ i ∈ Finset.range 16, stT267 (i+1)) + stT267 17 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 16
    simpa using h
  have hprev := st267_p16
  have hstep := st267_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p18 : ((3788475791377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT267 (i+1))
      = (∑ i ∈ Finset.range 17, stT267 (i+1)) + stT267 18 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 17
    simpa using h
  have hprev := st267_p17
  have hstep := st267_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p19 : ((3672847934019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT267 (i+1))
      = (∑ i ∈ Finset.range 18, stT267 (i+1)) + stT267 19 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 18
    simpa using h
  have hprev := st267_p18
  have hstep := st267_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p20 : ((2619108715257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT267 (i+1))
      = (∑ i ∈ Finset.range 19, stT267 (i+1)) + stT267 20 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 19
    simpa using h
  have hprev := st267_p19
  have hstep := st267_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p21 : ((3071538447951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT267 (i+1))
      = (∑ i ∈ Finset.range 20, stT267 (i+1)) + stT267 21 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 20
    simpa using h
  have hprev := st267_p20
  have hstep := st267_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p22 : ((940135938223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT267 (i+1))
      = (∑ i ∈ Finset.range 21, stT267 (i+1)) + stT267 22 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 21
    simpa using h
  have hprev := st267_p21
  have hstep := st267_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p23 : ((-155661197953/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT267 (i+1))
      = (∑ i ∈ Finset.range 22, stT267 (i+1)) + stT267 23 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 22
    simpa using h
  have hprev := st267_p22
  have hstep := st267_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p24 : ((88207180233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT267 (i+1))
      = (∑ i ∈ Finset.range 23, stT267 (i+1)) + stT267 24 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 23
    simpa using h
  have hprev := st267_p23
  have hstep := st267_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p25 : ((1887387180233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT267 (i+1))
      = (∑ i ∈ Finset.range 24, stT267 (i+1)) + stT267 25 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 24
    simpa using h
  have hprev := st267_p24
  have hstep := st267_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p26 : ((263482287049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT267 (i+1))
      = (∑ i ∈ Finset.range 25, stT267 (i+1)) + stT267 26 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 25
    simpa using h
  have hprev := st267_p25
  have hstep := st267_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p27 : ((875373213049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT267 (i+1))
      = (∑ i ∈ Finset.range 26, stT267 (i+1)) + stT267 27 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 26
    simpa using h
  have hprev := st267_p26
  have hstep := st267_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p28 : ((803068585069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT267 (i+1))
      = (∑ i ∈ Finset.range 27, stT267 (i+1)) + stT267 28 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 27
    simpa using h
  have hprev := st267_p27
  have hstep := st267_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p29 : ((976571131671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT267 (i+1))
      = (∑ i ∈ Finset.range 28, stT267 (i+1)) + stT267 29 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 28
    simpa using h
  have hprev := st267_p28
  have hstep := st267_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p30 : ((155005489091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT267 (i+1))
      = (∑ i ∈ Finset.range 29, stT267 (i+1)) + stT267 30 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 29
    simpa using h
  have hprev := st267_p29
  have hstep := st267_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p31 : ((892144789941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT267 (i+1))
      = (∑ i ∈ Finset.range 30, stT267 (i+1)) + stT267 31 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 30
    simpa using h
  have hprev := st267_p30
  have hstep := st267_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p32 : ((6113847907/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT267 (i+1))
      = (∑ i ∈ Finset.range 31, stT267 (i+1)) + stT267 32 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 31
    simpa using h
  have hprev := st267_p31
  have hstep := st267_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p33 : ((-3690275353/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT267 (i+1))
      = (∑ i ∈ Finset.range 32, stT267 (i+1)) + stT267 33 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 32
    simpa using h
  have hprev := st267_p32
  have hstep := st267_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p34 : ((169540687809/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT267 (i+1))
      = (∑ i ∈ Finset.range 33, stT267 (i+1)) + stT267 34 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 33
    simpa using h
  have hprev := st267_p33
  have hstep := st267_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p35 : ((973262052747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT267 (i+1))
      = (∑ i ∈ Finset.range 34, stT267 (i+1)) + stT267 35 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 34
    simpa using h
  have hprev := st267_p34
  have hstep := st267_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p36 : ((234641905023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT267 (i+1))
      = (∑ i ∈ Finset.range 35, stT267 (i+1)) + stT267 36 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 35
    simpa using h
  have hprev := st267_p35
  have hstep := st267_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p37 : ((-465812914277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT267 (i+1))
      = (∑ i ∈ Finset.range 36, stT267 (i+1)) + stT267 37 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 36
    simpa using h
  have hprev := st267_p36
  have hstep := st267_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p38 : ((-613252791197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT267 (i+1))
      = (∑ i ∈ Finset.range 37, stT267 (i+1)) + stT267 38 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 37
    simpa using h
  have hprev := st267_p37
  have hstep := st267_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p39 : ((-100411126731/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT267 (i+1))
      = (∑ i ∈ Finset.range 38, stT267 (i+1)) + stT267 39 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 38
    simpa using h
  have hprev := st267_p38
  have hstep := st267_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p40 : ((780482873907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT267 (i+1))
      = (∑ i ∈ Finset.range 39, stT267 (i+1)) + stT267 40 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 39
    simpa using h
  have hprev := st267_p39
  have hstep := st267_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p41 : ((2265366796137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT267 (i+1))
      = (∑ i ∈ Finset.range 40, stT267 (i+1)) + stT267 41 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 40
    simpa using h
  have hprev := st267_p40
  have hstep := st267_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p42 : ((473452857099/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT267 (i+1))
      = (∑ i ∈ Finset.range 41, stT267 (i+1)) + stT267 42 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 41
    simpa using h
  have hprev := st267_p41
  have hstep := st267_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p43 : ((2645969105051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT267 (i+1))
      = (∑ i ∈ Finset.range 42, stT267 (i+1)) + stT267 43 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 42
    simpa using h
  have hprev := st267_p42
  have hstep := st267_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p44 : ((3363890639369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT267 (i+1))
      = (∑ i ∈ Finset.range 43, stT267 (i+1)) + stT267 44 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 43
    simpa using h
  have hprev := st267_p43
  have hstep := st267_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p45 : ((1991088221509/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT267 (i+1))
      = (∑ i ∈ Finset.range 44, stT267 (i+1)) + stT267 45 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 44
    simpa using h
  have hprev := st267_p44
  have hstep := st267_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p46 : ((1750371258509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT267 (i+1))
      = (∑ i ∈ Finset.range 45, stT267 (i+1)) + stT267 46 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 45
    simpa using h
  have hprev := st267_p45
  have hstep := st267_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p47 : ((1756923509817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT267 (i+1))
      = (∑ i ∈ Finset.range 46, stT267 (i+1)) + stT267 47 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 46
    simpa using h
  have hprev := st267_p46
  have hstep := st267_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p48 : ((7923243949933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT267 (i+1))
      = (∑ i ∈ Finset.range 47, stT267 (i+1)) + stT267 48 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 47
    simpa using h
  have hprev := st267_p47
  have hstep := st267_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p49 : ((52091215653/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT267 (i+1))
      = (∑ i ∈ Finset.range 48, stT267 (i+1)) + stT267 49 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 48
    simpa using h
  have hprev := st267_p48
  have hstep := st267_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p50 : ((5462714192349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT267 (i+1))
      = (∑ i ∈ Finset.range 49, stT267 (i+1)) + stT267 50 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 49
    simpa using h
  have hprev := st267_p49
  have hstep := st267_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p51 : ((5686578356229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT267 (i+1))
      = (∑ i ∈ Finset.range 50, stT267 (i+1)) + stT267 51 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 50
    simpa using h
  have hprev := st267_p50
  have hstep := st267_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p52 : ((7006464818229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT267 (i+1))
      = (∑ i ∈ Finset.range 51, stT267 (i+1)) + stT267 52 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 51
    simpa using h
  have hprev := st267_p51
  have hstep := st267_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p53 : ((984444976423/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT267 (i+1))
      = (∑ i ∈ Finset.range 52, stT267 (i+1)) + stT267 53 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 52
    simpa using h
  have hprev := st267_p52
  have hstep := st267_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p54 : ((1774738240637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT267 (i+1))
      = (∑ i ∈ Finset.range 53, stT267 (i+1)) + stT267 54 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 53
    simpa using h
  have hprev := st267_p53
  have hstep := st267_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p55 : ((1466982458537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT267 (i+1))
      = (∑ i ∈ Finset.range 54, stT267 (i+1)) + stT267 55 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 54
    simpa using h
  have hprev := st267_p54
  have hstep := st267_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p56 : ((3145321087411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT267 (i+1))
      = (∑ i ∈ Finset.range 55, stT267 (i+1)) + stT267 56 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 55
    simpa using h
  have hprev := st267_p55
  have hstep := st267_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p57 : ((3776287071719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT267 (i+1))
      = (∑ i ∈ Finset.range 56, stT267 (i+1)) + stT267 57 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 56
    simpa using h
  have hprev := st267_p56
  have hstep := st267_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p58 : ((7068779283383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT267 (i+1))
      = (∑ i ∈ Finset.range 57, stT267 (i+1)) + stT267 58 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 57
    simpa using h
  have hprev := st267_p57
  have hstep := st267_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p59 : ((5942463470673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT267 (i+1))
      = (∑ i ∈ Finset.range 58, stT267 (i+1)) + stT267 59 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 58
    simpa using h
  have hprev := st267_p58
  have hstep := st267_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p60 : ((6822732893549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT267 (i+1))
      = (∑ i ∈ Finset.range 59, stT267 (i+1)) + stT267 60 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 59
    simpa using h
  have hprev := st267_p59
  have hstep := st267_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p61 : ((1492075584761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT267 (i+1))
      = (∑ i ∈ Finset.range 60, stT267 (i+1)) + stT267 61 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 60
    simpa using h
  have hprev := st267_p60
  have hstep := st267_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p62 : ((6204674876323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT267 (i+1))
      = (∑ i ∈ Finset.range 61, stT267 (i+1)) + stT267 62 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 61
    simpa using h
  have hprev := st267_p61
  have hstep := st267_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p63 : ((1312915000509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT267 (i+1))
      = (∑ i ∈ Finset.range 62, stT267 (i+1)) + stT267 63 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 62
    simpa using h
  have hprev := st267_p62
  have hstep := st267_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p64 : ((1487555250509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT267 (i+1))
      = (∑ i ∈ Finset.range 63, stT267 (i+1)) + stT267 64 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 63
    simpa using h
  have hprev := st267_p63
  have hstep := st267_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p65 : ((1244452003901/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT267 (i+1))
      = (∑ i ∈ Finset.range 64, stT267 (i+1)) + stT267 65 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 64
    simpa using h
  have hprev := st267_p64
  have hstep := st267_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p66 : ((6741230594701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT267 (i+1))
      = (∑ i ∈ Finset.range 65, stT267 (i+1)) + stT267 66 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 65
    simpa using h
  have hprev := st267_p65
  have hstep := st267_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p67 : ((7259599023983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT267 (i+1))
      = (∑ i ∈ Finset.range 66, stT267 (i+1)) + stT267 67 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 66
    simpa using h
  have hprev := st267_p66
  have hstep := st267_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p68 : ((190870422053/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT267 (i+1))
      = (∑ i ∈ Finset.range 67, stT267 (i+1)) + stT267 68 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 67
    simpa using h
  have hprev := st267_p67
  have hstep := st267_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p69 : ((3599061945911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT267 (i+1))
      = (∑ i ∈ Finset.range 68, stT267 (i+1)) + stT267 69 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 68
    simpa using h
  have hprev := st267_p68
  have hstep := st267_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p70 : ((6696736083383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT267 (i+1))
      = (∑ i ∈ Finset.range 69, stT267 (i+1)) + stT267 70 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 69
    simpa using h
  have hprev := st267_p69
  have hstep := st267_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p71 : ((6445954805399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT267 (i+1))
      = (∑ i ∈ Finset.range 70, stT267 (i+1)) + stT267 71 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 70
    simpa using h
  have hprev := st267_p70
  have hstep := st267_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p72 : ((455994074261/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT267 (i+1))
      = (∑ i ∈ Finset.range 71, stT267 (i+1)) + stT267 72 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 71
    simpa using h
  have hprev := st267_p71
  have hstep := st267_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p73 : ((1538666426819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT267 (i+1))
      = (∑ i ∈ Finset.range 72, stT267 (i+1)) + stT267 73 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 72
    simpa using h
  have hprev := st267_p72
  have hstep := st267_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p74 : ((1818962639939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT267 (i+1))
      = (∑ i ∈ Finset.range 73, stT267 (i+1)) + stT267 74 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 73
    simpa using h
  have hprev := st267_p73
  have hstep := st267_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p75 : ((1599936644857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT267 (i+1))
      = (∑ i ∈ Finset.range 74, stT267 (i+1)) + stT267 75 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 74
    simpa using h
  have hprev := st267_p74
  have hstep := st267_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p76 : ((691550611349/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT267 (i+1))
      = (∑ i ∈ Finset.range 75, stT267 (i+1)) + stT267 76 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 75
    simpa using h
  have hprev := st267_p75
  have hstep := st267_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p77 : ((339078695917/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT267 (i+1))
      = (∑ i ∈ Finset.range 76, stT267 (i+1)) + stT267 77 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 76
    simpa using h
  have hprev := st267_p76
  have hstep := st267_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p78 : ((3286136731159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT267 (i+1))
      = (∑ i ∈ Finset.range 77, stT267 (i+1)) + stT267 78 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 77
    simpa using h
  have hprev := st267_p77
  have hstep := st267_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p79 : ((7057117329011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT267 (i+1))
      = (∑ i ∈ Finset.range 78, stT267 (i+1)) + stT267 79 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 78
    simpa using h
  have hprev := st267_p78
  have hstep := st267_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p80 : ((6369338589299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT267 (i+1))
      = (∑ i ∈ Finset.range 79, stT267 (i+1)) + stT267 80 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 79
    simpa using h
  have hprev := st267_p79
  have hstep := st267_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p81 : ((3597496475589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT267 (i+1))
      = (∑ i ∈ Finset.range 80, stT267 (i+1)) + stT267 81 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 80
    simpa using h
  have hprev := st267_p80
  have hstep := st267_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p82 : ((3141293044987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT267 (i+1))
      = (∑ i ∈ Finset.range 81, stT267 (i+1)) + stT267 82 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 81
    simpa using h
  have hprev := st267_p81
  have hstep := st267_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p83 : ((3621924133379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT267 (i+1))
      = (∑ i ∈ Finset.range 82, stT267 (i+1)) + stT267 83 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 82
    simpa using h
  have hprev := st267_p82
  have hstep := st267_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p84 : ((3130108769339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT267 (i+1))
      = (∑ i ∈ Finset.range 83, stT267 (i+1)) + stT267 84 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 83
    simpa using h
  have hprev := st267_p83
  have hstep := st267_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p85 : ((3623160113631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT267 (i+1))
      = (∑ i ∈ Finset.range 84, stT267 (i+1)) + stT267 85 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 84
    simpa using h
  have hprev := st267_p84
  have hstep := st267_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p86 : ((3137227236187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT267 (i+1))
      = (∑ i ∈ Finset.range 85, stT267 (i+1)) + stT267 86 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 85
    simpa using h
  have hprev := st267_p85
  have hstep := st267_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p87 : ((3606848207939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT267 (i+1))
      = (∑ i ∈ Finset.range 86, stT267 (i+1)) + stT267 87 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 86
    simpa using h
  have hprev := st267_p86
  have hstep := st267_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p88 : ((3164873355503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT267 (i+1))
      = (∑ i ∈ Finset.range 87, stT267 (i+1)) + stT267 88 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 87
    simpa using h
  have hprev := st267_p87
  have hstep := st267_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p89 : ((7128137511403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT267 (i+1))
      = (∑ i ∈ Finset.range 88, stT267 (i+1)) + stT267 89 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 88
    simpa using h
  have hprev := st267_p88
  have hstep := st267_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p90 : ((6453326146477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT267 (i+1))
      = (∑ i ∈ Finset.range 89, stT267 (i+1)) + stT267 90 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 89
    simpa using h
  have hprev := st267_p89
  have hstep := st267_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p91 : ((6958960692457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT267 (i+1))
      = (∑ i ∈ Finset.range 90, stT267 (i+1)) + stT267 91 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 90
    simpa using h
  have hprev := st267_p90
  have hstep := st267_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p92 : ((6670937390331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT267 (i+1))
      = (∑ i ∈ Finset.range 91, stT267 (i+1)) + stT267 92 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 91
    simpa using h
  have hprev := st267_p91
  have hstep := st267_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p93 : ((6696566671247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT267 (i+1))
      = (∑ i ∈ Finset.range 92, stT267 (i+1)) + stT267 93 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 92
    simpa using h
  have hprev := st267_p92
  have hstep := st267_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p94 : ((6962848630817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT267 (i+1))
      = (∑ i ∈ Finset.range 93, stT267 (i+1)) + stT267 94 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 93
    simpa using h
  have hprev := st267_p93
  have hstep := st267_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p95 : ((6402811837793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT267 (i+1))
      = (∑ i ∈ Finset.range 94, stT267 (i+1)) + stT267 95 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 94
    simpa using h
  have hprev := st267_p94
  have hstep := st267_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p96 : ((7216684844393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT267 (i+1))
      = (∑ i ∈ Finset.range 95, stT267 (i+1)) + stT267 96 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 95
    simpa using h
  have hprev := st267_p95
  have hstep := st267_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p97 : ((6238879284371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT267 (i+1))
      = (∑ i ∈ Finset.range 96, stT267 (i+1)) + stT267 97 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 96
    simpa using h
  have hprev := st267_p96
  have hstep := st267_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p98 : ((7240437921307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT267 (i+1))
      = (∑ i ∈ Finset.range 97, stT267 (i+1)) + stT267 98 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 97
    simpa using h
  have hprev := st267_p97
  have hstep := st267_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p99 : ((6389421994807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT267 (i+1))
      = (∑ i ∈ Finset.range 98, stT267 (i+1)) + stT267 99 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 98
    simpa using h
  have hprev := st267_p98
  have hstep := st267_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p100 : ((216044139713/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT267 (i+1))
      = (∑ i ∈ Finset.range 99, stT267 (i+1)) + stT267 100 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 99
    simpa using h
  have hprev := st267_p99
  have hstep := st267_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p101 : ((1711747426041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT267 (i+1))
      = (∑ i ∈ Finset.range 100, stT267 (i+1)) + stT267 101 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 100
    simpa using h
  have hprev := st267_p100
  have hstep := st267_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p102 : ((1605342656443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT267 (i+1))
      = (∑ i ∈ Finset.range 101, stT267 (i+1)) + stT267 102 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 101
    simpa using h
  have hprev := st267_p101
  have hstep := st267_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p103 : ((3620088527057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT267 (i+1))
      = (∑ i ∈ Finset.range 102, stT267 (i+1)) + stT267 103 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 102
    simpa using h
  have hprev := st267_p102
  have hstep := st267_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p104 : ((3129964725827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT267 (i+1))
      = (∑ i ∈ Finset.range 103, stT267 (i+1)) + stT267 104 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 103
    simpa using h
  have hprev := st267_p103
  have hstep := st267_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p105 : ((3543722416277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT267 (i+1))
      = (∑ i ∈ Finset.range 104, stT267 (i+1)) + stT267 105 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 104
    simpa using h
  have hprev := st267_p104
  have hstep := st267_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p106 : ((3353943816023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT267 (i+1))
      = (∑ i ∈ Finset.range 105, stT267 (i+1)) + stT267 106 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 105
    simpa using h
  have hprev := st267_p105
  have hstep := st267_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p107 : ((6484533682303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT267 (i+1))
      = (∑ i ∈ Finset.range 106, stT267 (i+1)) + stT267 107 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 106
    simpa using h
  have hprev := st267_p106
  have hstep := st267_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p108 : ((7232795640553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT267 (i+1))
      = (∑ i ∈ Finset.range 107, stT267 (i+1)) + stT267 108 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 107
    simpa using h
  have hprev := st267_p107
  have hstep := st267_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p109 : ((6274920749203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT267 (i+1))
      = (∑ i ∈ Finset.range 108, stT267 (i+1)) + stT267 109 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 108
    simpa using h
  have hprev := st267_p108
  have hstep := st267_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p110 : ((7001580836339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT267 (i+1))
      = (∑ i ∈ Finset.range 109, stT267 (i+1)) + stT267 110 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 109
    simpa using h
  have hprev := st267_p109
  have hstep := st267_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p111 : ((6867767592341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT267 (i+1))
      = (∑ i ∈ Finset.range 110, stT267 (i+1)) + stT267 111 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 110
    simpa using h
  have hprev := st267_p110
  have hstep := st267_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p112 : ((6329844309333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT267 (i+1))
      = (∑ i ∈ Finset.range 111, stT267 (i+1)) + stT267 112 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 111
    simpa using h
  have hprev := st267_p111
  have hstep := st267_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p113 : ((7252323748533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT267 (i+1))
      = (∑ i ∈ Finset.range 112, stT267 (i+1)) + stT267 113 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 112
    simpa using h
  have hprev := st267_p112
  have hstep := st267_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p114 : ((6475162480867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT267 (i+1))
      = (∑ i ∈ Finset.range 113, stT267 (i+1)) + stT267 114 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 113
    simpa using h
  have hprev := st267_p113
  have hstep := st267_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p115 : ((6631896820683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT267 (i+1))
      = (∑ i ∈ Finset.range 114, stT267 (i+1)) + stT267 115 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 114
    simpa using h
  have hprev := st267_p114
  have hstep := st267_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p116 : ((1440365948619/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT267 (i+1))
      = (∑ i ∈ Finset.range 115, stT267 (i+1)) + stT267 116 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 115
    simpa using h
  have hprev := st267_p115
  have hstep := st267_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p117 : ((6278952166851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT267 (i+1))
      = (∑ i ∈ Finset.range 116, stT267 (i+1)) + stT267 117 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 116
    simpa using h
  have hprev := st267_p116
  have hstep := st267_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p118 : ((276568727619/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT267 (i+1))
      = (∑ i ∈ Finset.range 117, stT267 (i+1)) + stT267 118 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 117
    simpa using h
  have hprev := st267_p117
  have hstep := st267_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p119 : ((1406014096743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT267 (i+1))
      = (∑ i ∈ Finset.range 118, stT267 (i+1)) + stT267 119 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 118
    simpa using h
  have hprev := st267_p118
  have hstep := st267_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p120 : ((24982141813/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT267 (i+1))
      = (∑ i ∈ Finset.range 119, stT267 (i+1)) + stT267 120 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 119
    simpa using h
  have hprev := st267_p119
  have hstep := st267_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p121 : ((88583080379/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT267 (i+1))
      = (∑ i ∈ Finset.range 120, stT267 (i+1)) + stT267 121 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 120
    simpa using h
  have hprev := st267_p120
  have hstep := st267_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p122 : ((1718353675861/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT267 (i+1))
      = (∑ i ∈ Finset.range 121, stT267 (i+1)) + stT267 122 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 121
    simpa using h
  have hprev := st267_p121
  have hstep := st267_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p123 : ((1568980318651/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT267 (i+1))
      = (∑ i ∈ Finset.range 122, stT267 (i+1)) + stT267 123 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 122
    simpa using h
  have hprev := st267_p122
  have hstep := st267_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p124 : ((716595574123/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT267 (i+1))
      = (∑ i ∈ Finset.range 123, stT267 (i+1)) + stT267 124 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 123
    simpa using h
  have hprev := st267_p123
  have hstep := st267_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p125 : ((3392198167071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT267 (i+1))
      = (∑ i ∈ Finset.range 124, stT267 (i+1)) + stT267 125 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 124
    simpa using h
  have hprev := st267_p124
  have hstep := st267_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p126 : ((6301051600479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT267 (i+1))
      = (∑ i ∈ Finset.range 125, stT267 (i+1)) + stT267 126 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 125
    simpa using h
  have hprev := st267_p125
  have hstep := st267_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p127 : ((7187863651251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT267 (i+1))
      = (∑ i ∈ Finset.range 126, stT267 (i+1)) + stT267 127 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 126
    simpa using h
  have hprev := st267_p126
  have hstep := st267_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p128 : ((6772004184207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT267 (i+1))
      = (∑ i ∈ Finset.range 127, stT267 (i+1)) + stT267 128 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 127
    simpa using h
  have hprev := st267_p127
  have hstep := st267_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p129 : ((6293912247599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT267 (i+1))
      = (∑ i ∈ Finset.range 128, stT267 (i+1)) + stT267 129 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 128
    simpa using h
  have hprev := st267_p128
  have hstep := st267_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p130 : ((7167908438121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT267 (i+1))
      = (∑ i ∈ Finset.range 129, stT267 (i+1)) + stT267 130 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 129
    simpa using h
  have hprev := st267_p129
  have hstep := st267_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p131 : ((3416949439983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT267 (i+1))
      = (∑ i ∈ Finset.range 130, stT267 (i+1)) + stT267 131 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 130
    simpa using h
  have hprev := st267_p130
  have hstep := st267_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p132 : ((3130312934503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT267 (i+1))
      = (∑ i ∈ Finset.range 131, stT267 (i+1)) + stT267 132 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 131
    simpa using h
  have hprev := st267_p131
  have hstep := st267_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p133 : ((7095194869563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT267 (i+1))
      = (∑ i ∈ Finset.range 132, stT267 (i+1)) + stT267 133 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 132
    simpa using h
  have hprev := st267_p132
  have hstep := st267_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p134 : ((3481077362109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT267 (i+1))
      = (∑ i ∈ Finset.range 133, stT267 (i+1)) + stT267 134 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 133
    simpa using h
  have hprev := st267_p133
  have hstep := st267_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p135 : ((779626249859/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT267 (i+1))
      = (∑ i ∈ Finset.range 134, stT267 (i+1)) + stT267 135 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 134
    simpa using h
  have hprev := st267_p134
  have hstep := st267_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p136 : ((1735904641011/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT267 (i+1))
      = (∑ i ∈ Finset.range 135, stT267 (i+1)) + stT267 136 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 135
    simpa using h
  have hprev := st267_p135
  have hstep := st267_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p137 : ((7127459957661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT267 (i+1))
      = (∑ i ∈ Finset.range 136, stT267 (i+1)) + stT267 137 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 136
    simpa using h
  have hprev := st267_p136
  have hstep := st267_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p138 : ((6286246087747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT267 (i+1))
      = (∑ i ∈ Finset.range 137, stT267 (i+1)) + stT267 138 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 137
    simpa using h
  have hprev := st267_p137
  have hstep := st267_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p139 : ((6701090597607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT267 (i+1))
      = (∑ i ∈ Finset.range 138, stT267 (i+1)) + stT267 139 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 138
    simpa using h
  have hprev := st267_p138
  have hstep := st267_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p140 : ((7256098158483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT267 (i+1))
      = (∑ i ∈ Finset.range 139, stT267 (i+1)) + stT267 140 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 139
    simpa using h
  have hprev := st267_p139
  have hstep := st267_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p141 : ((6476166874699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT267 (i+1))
      = (∑ i ∈ Finset.range 140, stT267 (i+1)) + stT267 141 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 140
    simpa using h
  have hprev := st267_p140
  have hstep := st267_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p142 : ((6416762020101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT267 (i+1))
      = (∑ i ∈ Finset.range 141, stT267 (i+1)) + stT267 142 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 141
    simpa using h
  have hprev := st267_p141
  have hstep := st267_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p143 : ((7230537542529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT267 (i+1))
      = (∑ i ∈ Finset.range 142, stT267 (i+1)) + stT267 143 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 142
    simpa using h
  have hprev := st267_p142
  have hstep := st267_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p144 : ((6815038043463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT267 (i+1))
      = (∑ i ∈ Finset.range 143, stT267 (i+1)) + stT267 144 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 143
    simpa using h
  have hprev := st267_p143
  have hstep := st267_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p145 : ((6235759140943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT267 (i+1))
      = (∑ i ∈ Finset.range 144, stT267 (i+1)) + stT267 145 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 144
    simpa using h
  have hprev := st267_p144
  have hstep := st267_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p146 : ((3479481298899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT267 (i+1))
      = (∑ i ∈ Finset.range 145, stT267 (i+1)) + stT267 146 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 145
    simpa using h
  have hprev := st267_p145
  have hstep := st267_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p147 : ((895961708147/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT267 (i+1))
      = (∑ i ∈ Finset.range 146, stT267 (i+1)) + stT267 147 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 146
    simpa using h
  have hprev := st267_p146
  have hstep := st267_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p148 : ((6345770178741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT267 (i+1))
      = (∑ i ∈ Finset.range 147, stT267 (i+1)) + stT267 148 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 147
    simpa using h
  have hprev := st267_p147
  have hstep := st267_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p149 : ((651705417699/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT267 (i+1))
      = (∑ i ∈ Finset.range 148, stT267 (i+1)) + stT267 149 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 148
    simpa using h
  have hprev := st267_p148
  have hstep := st267_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p150 : ((3630297721447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT267 (i+1))
      = (∑ i ∈ Finset.range 149, stT267 (i+1)) + stT267 150 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 149
    simpa using h
  have hprev := st267_p149
  have hstep := st267_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p151 : ((135633677431/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT267 (i+1))
      = (∑ i ∈ Finset.range 150, stT267 (i+1)) + stT267 151 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 150
    simpa using h
  have hprev := st267_p150
  have hstep := st267_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p152 : ((622871910363/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT267 (i+1))
      = (∑ i ∈ Finset.range 151, stT267 (i+1)) + stT267 152 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 151
    simpa using h
  have hprev := st267_p151
  have hstep := st267_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p153 : ((3454648721169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT267 (i+1))
      = (∑ i ∈ Finset.range 152, stT267 (i+1)) + stT267 153 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 152
    simpa using h
  have hprev := st267_p152
  have hstep := st267_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p154 : ((3612053155717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT267 (i+1))
      = (∑ i ∈ Finset.range 153, stT267 (i+1)) + stT267 154 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 153
    simpa using h
  have hprev := st267_p153
  have hstep := st267_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p155 : ((3222323984347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT267 (i+1))
      = (∑ i ∈ Finset.range 154, stT267 (i+1)) + stT267 155 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 154
    simpa using h
  have hprev := st267_p154
  have hstep := st267_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p156 : ((6366432548763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT267 (i+1))
      = (∑ i ∈ Finset.range 155, stT267 (i+1)) + stT267 156 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 155
    simpa using h
  have hprev := st267_p155
  have hstep := st267_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p157 : ((7163918388091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT267 (i+1))
      = (∑ i ∈ Finset.range 156, stT267 (i+1)) + stT267 157 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 156
    simpa using h
  have hprev := st267_p156
  have hstep := st267_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p158 : ((1407124227221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT267 (i+1))
      = (∑ i ∈ Finset.range 157, stT267 (i+1)) + stT267 158 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 157
    simpa using h
  have hprev := st267_p157
  have hstep := st267_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p159 : ((6272475920077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT267 (i+1))
      = (∑ i ∈ Finset.range 158, stT267 (i+1)) + stT267 159 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 158
    simpa using h
  have hprev := st267_p158
  have hstep := st267_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p160 : ((1312969145759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT267 (i+1))
      = (∑ i ∈ Finset.range 159, stT267 (i+1)) + stT267 160 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 159
    simpa using h
  have hprev := st267_p159
  have hstep := st267_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p161 : ((1453376301407/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT267 (i+1))
      = (∑ i ∈ Finset.range 160, stT267 (i+1)) + stT267 161 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 160
    simpa using h
  have hprev := st267_p160
  have hstep := st267_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p162 : ((1370689350247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT267 (i+1))
      = (∑ i ∈ Finset.range 161, stT267 (i+1)) + stT267 162 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 161
    simpa using h
  have hprev := st267_p161
  have hstep := st267_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p163 : ((621884477273/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT267 (i+1))
      = (∑ i ∈ Finset.range 162, stT267 (i+1)) + stT267 163 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 162
    simpa using h
  have hprev := st267_p162
  have hstep := st267_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p164 : ((3357509616041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT267 (i+1))
      = (∑ i ∈ Finset.range 163, stT267 (i+1)) + stT267 164 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 163
    simpa using h
  have hprev := st267_p163
  have hstep := st267_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p165 : ((455587531623/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT267 (i+1))
      = (∑ i ∈ Finset.range 164, stT267 (i+1)) + stT267 165 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 164
    simpa using h
  have hprev := st267_p164
  have hstep := st267_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p166 : ((6741635818473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT267 (i+1))
      = (∑ i ∈ Finset.range 165, stT267 (i+1)) + stT267 166 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 165
    simpa using h
  have hprev := st267_p165
  have hstep := st267_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p167 : ((6211552449641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT267 (i+1))
      = (∑ i ∈ Finset.range 166, stT267 (i+1)) + stT267 167 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 166
    simpa using h
  have hprev := st267_p166
  have hstep := st267_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p168 : ((6785738573837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT267 (i+1))
      = (∑ i ∈ Finset.range 167, stT267 (i+1)) + stT267 168 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 167
    simpa using h
  have hprev := st267_p167
  have hstep := st267_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p169 : ((7291496529617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT267 (i+1))
      = (∑ i ∈ Finset.range 168, stT267 (i+1)) + stT267 169 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 168
    simpa using h
  have hprev := st267_p168
  have hstep := st267_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p170 : ((6711384144707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT267 (i+1))
      = (∑ i ∈ Finset.range 169, stT267 (i+1)) + stT267 170 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 169
    simpa using h
  have hprev := st267_p169
  have hstep := st267_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p171 : ((6208289386387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT267 (i+1))
      = (∑ i ∈ Finset.range 170, stT267 (i+1)) + stT267 171 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 170
    simpa using h
  have hprev := st267_p170
  have hstep := st267_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p172 : ((1355096709587/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT267 (i+1))
      = (∑ i ∈ Finset.range 171, stT267 (i+1)) + stT267 172 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 171
    simpa using h
  have hprev := st267_p171
  have hstep := st267_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p173 : ((729637837027/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT267 (i+1))
      = (∑ i ∈ Finset.range 172, stT267 (i+1)) + stT267 173 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 172
    simpa using h
  have hprev := st267_p172
  have hstep := st267_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p174 : ((6761003549777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT267 (i+1))
      = (∑ i ∈ Finset.range 173, stT267 (i+1)) + stT267 174 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 173
    simpa using h
  have hprev := st267_p173
  have hstep := st267_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p175 : ((3102225033799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT267 (i+1))
      = (∑ i ∈ Finset.range 174, stT267 (i+1)) + stT267 175 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 174
    simpa using h
  have hprev := st267_p174
  have hstep := st267_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p176 : ((3343249318189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT267 (i+1))
      = (∑ i ∈ Finset.range 175, stT267 (i+1)) + stT267 176 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 175
    simpa using h
  have hprev := st267_p175
  have hstep := st267_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p177 : ((3645594411813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT267 (i+1))
      = (∑ i ∈ Finset.range 176, stT267 (i+1)) + stT267 177 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 176
    simpa using h
  have hprev := st267_p176
  have hstep := st267_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p178 : ((3443552439723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT267 (i+1))
      = (∑ i ∈ Finset.range 177, stT267 (i+1)) + stT267 178 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 177
    simpa using h
  have hprev := st267_p177
  have hstep := st267_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p179 : ((3114557272783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT267 (i+1))
      = (∑ i ∈ Finset.range 178, stT267 (i+1)) + stT267 179 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 178
    simpa using h
  have hprev := st267_p178
  have hstep := st267_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p180 : ((6526869706321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT267 (i+1))
      = (∑ i ∈ Finset.range 179, stT267 (i+1)) + stT267 180 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 179
    simpa using h
  have hprev := st267_p179
  have hstep := st267_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p181 : ((1446504808291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT267 (i+1))
      = (∑ i ∈ Finset.range 180, stT267 (i+1)) + stT267 181 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 180
    simpa using h
  have hprev := st267_p180
  have hstep := st267_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p182 : ((1414186901291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT267 (i+1))
      = (∑ i ∈ Finset.range 181, stT267 (i+1)) + stT267 182 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 181
    simpa using h
  have hprev := st267_p181
  have hstep := st267_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p183 : ((6336302335853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT267 (i+1))
      = (∑ i ∈ Finset.range 182, stT267 (i+1)) + stT267 183 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 182
    simpa using h
  have hprev := st267_p182
  have hstep := st267_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p184 : ((6333453756413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT267 (i+1))
      = (∑ i ∈ Finset.range 183, stT267 (i+1)) + stT267 184 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 183
    simpa using h
  have hprev := st267_p183
  have hstep := st267_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p185 : ((7062668410173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT267 (i+1))
      = (∑ i ∈ Finset.range 184, stT267 (i+1)) + stT267 185 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 184
    simpa using h
  have hprev := st267_p184
  have hstep := st267_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p186 : ((3625174720239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT267 (i+1))
      = (∑ i ∈ Finset.range 185, stT267 (i+1)) + stT267 186 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 185
    simpa using h
  have hprev := st267_p185
  have hstep := st267_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p187 : ((6576208606149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT267 (i+1))
      = (∑ i ∈ Finset.range 186, stT267 (i+1)) + stT267 187 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 186
    simpa using h
  have hprev := st267_p186
  have hstep := st267_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p188 : ((6198174661599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT267 (i+1))
      = (∑ i ∈ Finset.range 187, stT267 (i+1)) + stT267 188 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 187
    simpa using h
  have hprev := st267_p187
  have hstep := st267_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p189 : ((6754863034431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT267 (i+1))
      = (∑ i ∈ Finset.range 188, stT267 (i+1)) + stT267 189 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 188
    simpa using h
  have hprev := st267_p188
  have hstep := st267_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p190 : ((7305103934011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT267 (i+1))
      = (∑ i ∈ Finset.range 189, stT267 (i+1)) + stT267 190 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 189
    simpa using h
  have hprev := st267_p189
  have hstep := st267_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p191 : ((3466347538293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT267 (i+1))
      = (∑ i ∈ Finset.range 190, stT267 (i+1)) + stT267 191 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 190
    simpa using h
  have hprev := st267_p190
  have hstep := st267_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p192 : ((3129131242569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT267 (i+1))
      = (∑ i ∈ Finset.range 191, stT267 (i+1)) + stT267 192 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 191
    simpa using h
  have hprev := st267_p191
  have hstep := st267_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p193 : ((3193632425089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT267 (i+1))
      = (∑ i ∈ Finset.range 192, stT267 (i+1)) + stT267 193 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 192
    simpa using h
  have hprev := st267_p192
  have hstep := st267_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p194 : ((55508953349/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT267 (i+1))
      = (∑ i ∈ Finset.range 193, stT267 (i+1)) + stT267 194 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 193
    simpa using h
  have hprev := st267_p193
  have hstep := st267_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p195 : ((906688815899/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT267 (i+1))
      = (∑ i ∈ Finset.range 194, stT267 (i+1)) + stT267 195 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 194
    simpa using h
  have hprev := st267_p194
  have hstep := st267_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p196 : ((131989533883/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT267 (i+1))
      = (∑ i ∈ Finset.range 195, stT267 (i+1)) + stT267 196 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 195
    simpa using h
  have hprev := st267_p195
  have hstep := st267_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p197 : ((6182106195053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT267 (i+1))
      = (∑ i ∈ Finset.range 196, stT267 (i+1)) + stT267 197 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 196
    simpa using h
  have hprev := st267_p196
  have hstep := st267_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p198 : ((1663479658371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT267 (i+1))
      = (∑ i ∈ Finset.range 197, stT267 (i+1)) + stT267 198 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 197
    simpa using h
  have hprev := st267_p197
  have hstep := st267_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p199 : ((454740872567/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT267 (i+1))
      = (∑ i ∈ Finset.range 198, stT267 (i+1)) + stT267 199 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 198
    simpa using h
  have hprev := st267_p198
  have hstep := st267_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p200 : ((1417725092501/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT267 (i+1))
      = (∑ i ∈ Finset.range 199, stT267 (i+1)) + stT267 200 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 199
    simpa using h
  have hprev := st267_p199
  have hstep := st267_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p201 : ((1276707382759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT267 (i+1))
      = (∑ i ∈ Finset.range 200, stT267 (i+1)) + stT267 201 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 200
    simpa using h
  have hprev := st267_p200
  have hstep := st267_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p202 : ((49856474403/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT267 (i+1))
      = (∑ i ∈ Finset.range 201, stT267 (i+1)) + stT267 202 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 201
    simpa using h
  have hprev := st267_p201
  have hstep := st267_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p203 : ((6858033875349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT267 (i+1))
      = (∑ i ∈ Finset.range 202, stT267 (i+1)) + stT267 203 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 202
    simpa using h
  have hprev := st267_p202
  have hstep := st267_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p204 : ((7323839117769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT267 (i+1))
      = (∑ i ∈ Finset.range 203, stT267 (i+1)) + stT267 204 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 203
    simpa using h
  have hprev := st267_p203
  have hstep := st267_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p205 : ((86780158481/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT267 (i+1))
      = (∑ i ∈ Finset.range 204, stT267 (i+1)) + stT267 205 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 204
    simpa using h
  have hprev := st267_p204
  have hstep := st267_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p206 : ((3139019941289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT267 (i+1))
      = (∑ i ∈ Finset.range 205, stT267 (i+1)) + stT267 206 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 205
    simpa using h
  have hprev := st267_p205
  have hstep := st267_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p207 : ((3148843402197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT267 (i+1))
      = (∑ i ∈ Finset.range 206, stT267 (i+1)) + stT267 207 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 206
    simpa using h
  have hprev := st267_p206
  have hstep := st267_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p208 : ((6968479274019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT267 (i+1))
      = (∑ i ∈ Finset.range 207, stT267 (i+1)) + stT267 208 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 207
    simpa using h
  have hprev := st267_p207
  have hstep := st267_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p209 : ((7327593664543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT267 (i+1))
      = (∑ i ∈ Finset.range 208, stT267 (i+1)) + stT267 209 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 208
    simpa using h
  have hprev := st267_p208
  have hstep := st267_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p210 : ((6868127709829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT267 (i+1))
      = (∑ i ∈ Finset.range 209, stT267 (i+1)) + stT267 210 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 209
    simpa using h
  have hprev := st267_p209
  have hstep := st267_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p211 : ((1560308828213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT267 (i+1))
      = (∑ i ∈ Finset.range 210, stT267 (i+1)) + stT267 211 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 210
    simpa using h
  have hprev := st267_p210
  have hstep := st267_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p212 : ((1580472648131/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT267 (i+1))
      = (∑ i ∈ Finset.range 211, stT267 (i+1)) + stT267 212 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 211
    simpa using h
  have hprev := st267_p211
  have hstep := st267_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p213 : ((1748462588249/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT267 (i+1))
      = (∑ i ∈ Finset.range 212, stT267 (i+1)) + stT267 213 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 212
    simpa using h
  have hprev := st267_p212
  have hstep := st267_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p214 : ((3665775456593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT267 (i+1))
      = (∑ i ∈ Finset.range 213, stT267 (i+1)) + stT267 214 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 213
    simpa using h
  have hprev := st267_p213
  have hstep := st267_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p215 : ((6877734390311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT267 (i+1))
      = (∑ i ∈ Finset.range 214, stT267 (i+1)) + stT267 215 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 214
    simpa using h
  have hprev := st267_p214
  have hstep := st267_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p216 : ((1249998383693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT267 (i+1))
      = (∑ i ∈ Finset.range 215, stT267 (i+1)) + stT267 216 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 215
    simpa using h
  have hprev := st267_p215
  have hstep := st267_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p217 : ((6289740271197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT267 (i+1))
      = (∑ i ∈ Finset.range 216, stT267 (i+1)) + stT267 217 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 216
    simpa using h
  have hprev := st267_p216
  have hstep := st267_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p218 : ((1734937920383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT267 (i+1))
      = (∑ i ∈ Finset.range 217, stT267 (i+1)) + stT267 218 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 217
    simpa using h
  have hprev := st267_p217
  have hstep := st267_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p219 : ((1834918615429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT267 (i+1))
      = (∑ i ∈ Finset.range 218, stT267 (i+1)) + stT267 219 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 218
    simpa using h
  have hprev := st267_p218
  have hstep := st267_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p220 : ((1742117176579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT267 (i+1))
      = (∑ i ∈ Finset.range 219, stT267 (i+1)) + stT267 220 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 219
    simpa using h
  have hprev := st267_p219
  have hstep := st267_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p221 : ((1578108736411/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT267 (i+1))
      = (∑ i ∈ Finset.range 220, stT267 (i+1)) + stT267 221 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 220
    simpa using h
  have hprev := st267_p220
  have hstep := st267_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p222 : ((6217225284781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT267 (i+1))
      = (∑ i ∈ Finset.range 221, stT267 (i+1)) + stT267 222 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 221
    simpa using h
  have hprev := st267_p221
  have hstep := st267_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p223 : ((425038424259/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT267 (i+1))
      = (∑ i ∈ Finset.range 222, stT267 (i+1)) + stT267 223 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 222
    simpa using h
  have hprev := st267_p222
  have hstep := st267_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p224 : ((731946365507/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT267 (i+1))
      = (∑ i ∈ Finset.range 223, stT267 (i+1)) + stT267 224 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 223
    simpa using h
  have hprev := st267_p223
  have hstep := st267_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p225 : ((3561181111593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT267 (i+1))
      = (∑ i ∈ Finset.range 224, stT267 (i+1)) + stT267 225 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 224
    simpa using h
  have hprev := st267_p224
  have hstep := st267_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p226 : ((6459635755841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT267 (i+1))
      = (∑ i ∈ Finset.range 225, stT267 (i+1)) + stT267 226 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 225
    simpa using h
  have hprev := st267_p225
  have hstep := st267_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p227 : ((6153895941309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT267 (i+1))
      = (∑ i ∈ Finset.range 226, stT267 (i+1)) + stT267 227 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 226
    simpa using h
  have hprev := st267_p226
  have hstep := st267_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p228 : ((1315589766941/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT267 (i+1))
      = (∑ i ∈ Finset.range 227, stT267 (i+1)) + stT267 228 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 227
    simpa using h
  have hprev := st267_p227
  have hstep := st267_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p229 : ((7210635151627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT267 (i+1))
      = (∑ i ∈ Finset.range 228, stT267 (i+1)) + stT267 229 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 228
    simpa using h
  have hprev := st267_p228
  have hstep := st267_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p230 : ((7286088664407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT267 (i+1))
      = (∑ i ∈ Finset.range 229, stT267 (i+1)) + stT267 230 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 229
    simpa using h
  have hprev := st267_p229
  have hstep := st267_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p231 : ((1343486650379/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT267 (i+1))
      = (∑ i ∈ Finset.range 230, stT267 (i+1)) + stT267 231 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 230
    simpa using h
  have hprev := st267_p230
  have hstep := st267_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p232 : ((6185420926807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT267 (i+1))
      = (∑ i ∈ Finset.range 231, stT267 (i+1)) + stT267 232 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 231
    simpa using h
  have hprev := st267_p231
  have hstep := st267_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p233 : ((197435935617/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT267 (i+1))
      = (∑ i ∈ Finset.range 232, stT267 (i+1)) + stT267 233 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 232
    simpa using h
  have hprev := st267_p232
  have hstep := st267_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p234 : ((217355274307/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT267 (i+1))
      = (∑ i ∈ Finset.range 233, stT267 (i+1)) + stT267 234 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 233
    simpa using h
  have hprev := st267_p233
  have hstep := st267_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p235 : ((459568893251/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT267 (i+1))
      = (∑ i ∈ Finset.range 234, stT267 (i+1)) + stT267 235 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 234
    simpa using h
  have hprev := st267_p234
  have hstep := st267_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p236 : ((3526816220493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT267 (i+1))
      = (∑ i ∈ Finset.range 235, stT267 (i+1)) + stT267 236 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 235
    simpa using h
  have hprev := st267_p235
  have hstep := st267_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p237 : ((3202227390633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT267 (i+1))
      = (∑ i ∈ Finset.range 236, stT267 (i+1)) + stT267 237 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 236
    simpa using h
  have hprev := st267_p236
  have hstep := st267_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p238 : ((3072892218819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT267 (i+1))
      = (∑ i ∈ Finset.range 237, stT267 (i+1)) + stT267 238 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 237
    simpa using h
  have hprev := st267_p237
  have hstep := st267_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p239 : ((820866535559/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT267 (i+1))
      = (∑ i ∈ Finset.range 238, stT267 (i+1)) + stT267 239 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 238
    simpa using h
  have hprev := st267_p238
  have hstep := st267_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p240 : ((1438366165941/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT267 (i+1))
      = (∑ i ∈ Finset.range 239, stT267 (i+1)) + stT267 240 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 239
    simpa using h
  have hprev := st267_p239
  have hstep := st267_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p241 : ((7324506352713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT267 (i+1))
      = (∑ i ∈ Finset.range 240, stT267 (i+1)) + stT267 241 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 240
    simpa using h
  have hprev := st267_p240
  have hstep := st267_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p242 : ((6821696351613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT267 (i+1))
      = (∑ i ∈ Finset.range 241, stT267 (i+1)) + stT267 242 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 241
    simpa using h
  have hprev := st267_p241
  have hstep := st267_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p243 : ((6238113910899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT267 (i+1))
      = (∑ i ∈ Finset.range 242, stT267 (i+1)) + stT267 243 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 242
    simpa using h
  have hprev := st267_p242
  have hstep := st267_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p244 : ((3104334941097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT267 (i+1))
      = (∑ i ∈ Finset.range 243, stT267 (i+1)) + stT267 244 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 243
    simpa using h
  have hprev := st267_p243
  have hstep := st267_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p245 : ((3380777864049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT267 (i+1))
      = (∑ i ∈ Finset.range 244, stT267 (i+1)) + stT267 245 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 244
    simpa using h
  have hprev := st267_p244
  have hstep := st267_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p246 : ((3650374006557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT267 (i+1))
      = (∑ i ∈ Finset.range 245, stT267 (i+1)) + stT267 246 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 245
    simpa using h
  have hprev := st267_p245
  have hstep := st267_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p247 : ((7252903835109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT267 (i+1))
      = (∑ i ∈ Finset.range 246, stT267 (i+1)) + stT267 247 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 246
    simpa using h
  have hprev := st267_p246
  have hstep := st267_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p248 : ((1668058221417/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT267 (i+1))
      = (∑ i ∈ Finset.range 247, stT267 (i+1)) + stT267 248 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 247
    simpa using h
  have hprev := st267_p247
  have hstep := st267_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p249 : ((6170647786593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT267 (i+1))
      = (∑ i ∈ Finset.range 248, stT267 (i+1)) + stT267 249 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 248
    simpa using h
  have hprev := st267_p248
  have hstep := st267_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p250 : ((6269508092553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT267 (i+1))
      = (∑ i ∈ Finset.range 249, stT267 (i+1)) + stT267 250 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 249
    simpa using h
  have hprev := st267_p249
  have hstep := st267_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p251 : ((6862850650761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT267 (i+1))
      = (∑ i ∈ Finset.range 250, stT267 (i+1)) + stT267 251 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 250
    simpa using h
  have hprev := st267_p250
  have hstep := st267_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p252 : ((7339022296761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT267 (i+1))
      = (∑ i ∈ Finset.range 251, stT267 (i+1)) + stT267 252 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 251
    simpa using h
  have hprev := st267_p251
  have hstep := st267_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p253 : ((1803472496859/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT267 (i+1))
      = (∑ i ∈ Finset.range 252, stT267 (i+1)) + stT267 253 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 252
    simpa using h
  have hprev := st267_p252
  have hstep := st267_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p254 : ((1654426755483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT267 (i+1))
      = (∑ i ∈ Finset.range 253, stT267 (i+1)) + stT267 254 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 253
    simpa using h
  have hprev := st267_p253
  have hstep := st267_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p255 : ((6151827559407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT267 (i+1))
      = (∑ i ∈ Finset.range 254, stT267 (i+1)) + stT267 255 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 254
    simpa using h
  have hprev := st267_p254
  have hstep := st267_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p256 : ((6279714434407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT267 (i+1))
      = (∑ i ∈ Finset.range 255, stT267 (i+1)) + stT267 256 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 255
    simpa using h
  have hprev := st267_p255
  have hstep := st267_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p257 : ((6871060394189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT267 (i+1))
      = (∑ i ∈ Finset.range 256, stT267 (i+1)) + stT267 257 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 256
    simpa using h
  have hprev := st267_p256
  have hstep := st267_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p258 : ((7341883582049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT267 (i+1))
      = (∑ i ∈ Finset.range 257, stT267 (i+1)) + stT267 258 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 257
    simpa using h
  have hprev := st267_p257
  have hstep := st267_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p259 : ((7233517896789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT267 (i+1))
      = (∑ i ∈ Finset.range 258, stT267 (i+1)) + stT267 259 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 258
    simpa using h
  have hprev := st267_p258
  have hstep := st267_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p260 : ((6654531512651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT267 (i+1))
      = (∑ i ∈ Finset.range 259, stT267 (i+1)) + stT267 260 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 259
    simpa using h
  have hprev := st267_p259
  have hstep := st267_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p261 : ((6164869810731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT267 (i+1))
      = (∑ i ∈ Finset.range 260, stT267 (i+1)) + stT267 261 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 260
    simpa using h
  have hprev := st267_p260
  have hstep := st267_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p262 : ((6231773442717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT267 (i+1))
      = (∑ i ∈ Finset.range 261, stT267 (i+1)) + stT267 262 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 261
    simpa using h
  have hprev := st267_p261
  have hstep := st267_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p263 : ((6788288273733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT267 (i+1))
      = (∑ i ∈ Finset.range 262, stT267 (i+1)) + stT267 263 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 262
    simpa using h
  have hprev := st267_p262
  have hstep := st267_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p264 : ((456688253167/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT267 (i+1))
      = (∑ i ∈ Finset.range 263, stT267 (i+1)) + stT267 264 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 263
    simpa using h
  have hprev := st267_p263
  have hstep := st267_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p265 : ((912847520691/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT267 (i+1))
      = (∑ i ∈ Finset.range 264, stT267 (i+1)) + stT267 265 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 264
    simpa using h
  have hprev := st267_p264
  have hstep := st267_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p266 : ((52989930771/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT267 (i+1))
      = (∑ i ∈ Finset.range 265, stT267 (i+1)) + stT267 266 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 265
    simpa using h
  have hprev := st267_p265
  have hstep := st267_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p267 : ((6229912520199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT267 (i+1))
      = (∑ i ∈ Finset.range 266, stT267 (i+1)) + stT267 267 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 266
    simpa using h
  have hprev := st267_p266
  have hstep := st267_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p268 : ((6151235297799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT267 (i+1))
      = (∑ i ∈ Finset.range 267, stT267 (i+1)) + stT267 268 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 267
    simpa using h
  have hprev := st267_p267
  have hstep := st267_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p269 : ((6615373377039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT267 (i+1))
      = (∑ i ∈ Finset.range 268, stT267 (i+1)) + stT267 269 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 268
    simpa using h
  have hprev := st267_p268
  have hstep := st267_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p270 : ((7199332664559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT267 (i+1))
      = (∑ i ∈ Finset.range 269, stT267 (i+1)) + stT267 270 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 269
    simpa using h
  have hprev := st267_p269
  have hstep := st267_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p271 : ((1475587497027/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT267 (i+1))
      = (∑ i ∈ Finset.range 270, stT267 (i+1)) + stT267 271 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 270
    simpa using h
  have hprev := st267_p270
  have hstep := st267_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p272 : ((279772998547/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT267 (i+1))
      = (∑ i ∈ Finset.range 271, stT267 (i+1)) + stT267 272 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 271
    simpa using h
  have hprev := st267_p271
  have hstep := st267_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p273 : ((1278347151551/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT267 (i+1))
      = (∑ i ∈ Finset.range 272, stT267 (i+1)) + stT267 273 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 272
    simpa using h
  have hprev := st267_p272
  have hstep := st267_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p274 : ((6101759134247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT267 (i+1))
      = (∑ i ∈ Finset.range 273, stT267 (i+1)) + stT267 274 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 273
    simpa using h
  have hprev := st267_p273
  have hstep := st267_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p275 : ((6375936956053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT267 (i+1))
      = (∑ i ∈ Finset.range 274, stT267 (i+1)) + stT267 275 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 274
    simpa using h
  have hprev := st267_p274
  have hstep := st267_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p276 : ((6972789286867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT267 (i+1))
      = (∑ i ∈ Finset.range 275, stT267 (i+1)) + stT267 276 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 275
    simpa using h
  have hprev := st267_p275
  have hstep := st267_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p277 : ((7375548631033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT267 (i+1))
      = (∑ i ∈ Finset.range 276, stT267 (i+1)) + stT267 277 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 276
    simpa using h
  have hprev := st267_p276
  have hstep := st267_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p278 : ((3620139567427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT267 (i+1))
      = (∑ i ∈ Finset.range 277, stT267 (i+1)) + stT267 278 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 277
    simpa using h
  have hprev := st267_p277
  have hstep := st267_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p279 : ((3342656254147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT267 (i+1))
      = (∑ i ∈ Finset.range 278, stT267 (i+1)) + stT267 279 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 278
    simpa using h
  have hprev := st267_p278
  have hstep := st267_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p280 : ((1545589034651/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT267 (i+1))
      = (∑ i ∈ Finset.range 279, stT267 (i+1)) + stT267 280 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 279
    simpa using h
  have hprev := st267_p279
  have hstep := st267_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p281 : ((769190311363/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT267 (i+1))
      = (∑ i ∈ Finset.range 280, stT267 (i+1)) + stT267 281 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 280
    simpa using h
  have hprev := st267_p280
  have hstep := st267_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p282 : ((3310013283679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT267 (i+1))
      = (∑ i ∈ Finset.range 281, stT267 (i+1)) + stT267 282 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 281
    simpa using h
  have hprev := st267_p281
  have hstep := st267_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p283 : ((3596088354493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT267 (i+1))
      = (∑ i ∈ Finset.range 282, stT267 (i+1)) + stT267 283 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 282
    simpa using h
  have hprev := st267_p282
  have hstep := st267_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p284 : ((3699052200513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT267 (i+1))
      = (∑ i ∈ Finset.range 283, stT267 (i+1)) + stT267 284 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 283
    simpa using h
  have hprev := st267_p283
  have hstep := st267_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p285 : ((1414293196861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT267 (i+1))
      = (∑ i ∈ Finset.range 284, stT267 (i+1)) + stT267 285 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 284
    simpa using h
  have hprev := st267_p284
  have hstep := st267_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p286 : ((202528414801/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT267 (i+1))
      = (∑ i ∈ Finset.range 285, stT267 (i+1)) + stT267 286 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 285
    simpa using h
  have hprev := st267_p285
  have hstep := st267_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p287 : ((1526238191253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT267 (i+1))
      = (∑ i ∈ Finset.range 286, stT267 (i+1)) + stT267 287 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 286
    simpa using h
  have hprev := st267_p286
  have hstep := st267_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p288 : ((3121997276661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT267 (i+1))
      = (∑ i ∈ Finset.range 287, stT267 (i+1)) + stT267 288 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 287
    simpa using h
  have hprev := st267_p287
  have hstep := st267_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p289 : ((6784134871487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT267 (i+1))
      = (∑ i ∈ Finset.range 288, stT267 (i+1)) + stT267 289 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 288
    simpa using h
  have hprev := st267_p288
  have hstep := st267_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p290 : ((7295090261207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT267 (i+1))
      = (∑ i ∈ Finset.range 289, stT267 (i+1)) + stT267 290 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 289
    simpa using h
  have hprev := st267_p289
  have hstep := st267_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p291 : ((7374810131527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT267 (i+1))
      = (∑ i ∈ Finset.range 290, stT267 (i+1)) + stT267 291 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 290
    simpa using h
  have hprev := st267_p290
  have hstep := st267_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p292 : ((6963423188059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT267 (i+1))
      = (∑ i ∈ Finset.range 291, stT267 (i+1)) + stT267 292 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 291
    simpa using h
  have hprev := st267_p291
  have hstep := st267_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p293 : ((6383496088541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT267 (i+1))
      = (∑ i ∈ Finset.range 292, stT267 (i+1)) + stT267 293 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 292
    simpa using h
  have hprev := st267_p292
  have hstep := st267_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p294 : ((6083830681913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT267 (i+1))
      = (∑ i ∈ Finset.range 293, stT267 (i+1)) + stT267 294 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 293
    simpa using h
  have hprev := st267_p293
  have hstep := st267_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p295 : ((6292741833287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT267 (i+1))
      = (∑ i ∈ Finset.range 294, stT267 (i+1)) + stT267 295 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 294
    simpa using h
  have hprev := st267_p294
  have hstep := st267_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p296 : ((1369591677853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT267 (i+1))
      = (∑ i ∈ Finset.range 295, stT267 (i+1)) + stT267 296 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 295
    simpa using h
  have hprev := st267_p295
  have hstep := st267_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p297 : ((7326731005839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT267 (i+1))
      = (∑ i ∈ Finset.range 296, stT267 (i+1)) + stT267 297 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 296
    simpa using h
  have hprev := st267_p296
  have hstep := st267_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p298 : ((7368955595883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT267 (i+1))
      = (∑ i ∈ Finset.range 297, stT267 (i+1)) + stT267 298 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 297
    simpa using h
  have hprev := st267_p297
  have hstep := st267_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p299 : ((6945514509513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT267 (i+1))
      = (∑ i ∈ Finset.range 298, stT267 (i+1)) + stT267 299 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 298
    simpa using h
  have hprev := st267_p298
  have hstep := st267_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p300 : ((6373958958851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT267 (i+1))
      = (∑ i ∈ Finset.range 299, stT267 (i+1)) + stT267 300 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 299
    simpa using h
  have hprev := st267_p299
  have hstep := st267_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p301 : ((3038765433099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT267 (i+1))
      = (∑ i ∈ Finset.range 300, stT267 (i+1)) + stT267 301 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 300
    simpa using h
  have hprev := st267_p300
  have hstep := st267_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p302 : ((6272367978283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT267 (i+1))
      = (∑ i ∈ Finset.range 301, stT267 (i+1)) + stT267 302 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 301
    simpa using h
  have hprev := st267_p301
  have hstep := st267_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p303 : ((6813422179839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT267 (i+1))
      = (∑ i ∈ Finset.range 302, stT267 (i+1)) + stT267 303 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 302
    simpa using h
  have hprev := st267_p302
  have hstep := st267_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p304 : ((3653093407387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT267 (i+1))
      = (∑ i ∈ Finset.range 303, stT267 (i+1)) + stT267 304 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 303
    simpa using h
  have hprev := st267_p303
  have hstep := st267_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p305 : ((1848908516537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT267 (i+1))
      = (∑ i ∈ Finset.range 304, stT267 (i+1)) + stT267 305 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 304
    simpa using h
  have hprev := st267_p304
  have hstep := st267_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p306 : ((109686117239/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT267 (i+1))
      = (∑ i ∈ Finset.range 305, stT267 (i+1)) + stT267 306 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 305
    simpa using h
  have hprev := st267_p305
  have hstep := st267_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p307 : ((3224619358929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT267 (i+1))
      = (∑ i ∈ Finset.range 306, stT267 (i+1)) + stT267 307 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 306
    simpa using h
  have hprev := st267_p306
  have hstep := st267_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p308 : ((1522166559963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT267 (i+1))
      = (∑ i ∈ Finset.range 307, stT267 (i+1)) + stT267 308 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 307
    simpa using h
  have hprev := st267_p307
  have hstep := st267_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p309 : ((1547673859183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT267 (i+1))
      = (∑ i ∈ Finset.range 308, stT267 (i+1)) + stT267 309 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 308
    simpa using h
  have hprev := st267_p308
  have hstep := st267_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p310 : ((6681355240749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT267 (i+1))
      = (∑ i ∈ Finset.range 309, stT267 (i+1)) + stT267 310 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 309
    simpa using h
  have hprev := st267_p309
  have hstep := st267_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p311 : ((7217374563003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT267 (i+1))
      = (∑ i ∈ Finset.range 310, stT267 (i+1)) + stT267 311 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 310
    simpa using h
  have hprev := st267_p310
  have hstep := st267_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p312 : ((7428119999641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT267 (i+1))
      = (∑ i ∈ Finset.range 311, stT267 (i+1)) + stT267 312 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 311
    simpa using h
  have hprev := st267_p311
  have hstep := st267_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p313 : ((7170638390387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT267 (i+1))
      = (∑ i ∈ Finset.range 312, stT267 (i+1)) + stT267 313 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 312
    simpa using h
  have hprev := st267_p312
  have hstep := st267_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p314 : ((1324659039937/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT267 (i+1))
      = (∑ i ∈ Finset.range 313, stT267 (i+1)) + stT267 314 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 313
    simpa using h
  have hprev := st267_p313
  have hstep := st267_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p315 : ((384945388791/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT267 (i+1))
      = (∑ i ∈ Finset.range 314, stT267 (i+1)) + stT267 315 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 314
    simpa using h
  have hprev := st267_p314
  have hstep := st267_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p316 : ((380673921881/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT267 (i+1))
      = (∑ i ∈ Finset.range 315, stT267 (i+1)) + stT267 316 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 315
    simpa using h
  have hprev := st267_p315
  have hstep := st267_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p317 : ((3230940282503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT267 (i+1))
      = (∑ i ∈ Finset.range 316, stT267 (i+1)) + stT267 317 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 316
    simpa using h
  have hprev := st267_p316
  have hstep := st267_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p318 : ((3511303290851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT267 (i+1))
      = (∑ i ∈ Finset.range 317, stT267 (i+1)) + stT267 318 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 317
    simpa using h
  have hprev := st267_p317
  have hstep := st267_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p319 : ((3700152062991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT267 (i+1))
      = (∑ i ∈ Finset.range 318, stT267 (i+1)) + stT267 319 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 318
    simpa using h
  have hprev := st267_p318
  have hstep := st267_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p320 : ((11479920993/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT267 (i+1))
      = (∑ i ∈ Finset.range 319, stT267 (i+1)) + stT267 320 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 319
    simpa using h
  have hprev := st267_p319
  have hstep := st267_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p321 : ((862534706833/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT267 (i+1))
      = (∑ i ∈ Finset.range 320, stT267 (i+1)) + stT267 321 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 320
    simpa using h
  have hprev := st267_p320
  have hstep := st267_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p322 : ((6352785031183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT267 (i+1))
      = (∑ i ∈ Finset.range 321, stT267 (i+1)) + stT267 322 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 321
    simpa using h
  have hprev := st267_p321
  have hstep := st267_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p323 : ((1514897901497/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT267 (i+1))
      = (∑ i ∈ Finset.range 322, stT267 (i+1)) + stT267 323 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 322
    simpa using h
  have hprev := st267_p322
  have hstep := st267_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p324 : ((1551993419957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT267 (i+1))
      = (∑ i ∈ Finset.range 323, stT267 (i+1)) + stT267 324 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 323
    simpa using h
  have hprev := st267_p323
  have hstep := st267_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p325 : ((1675144585757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT267 (i+1))
      = (∑ i ∈ Finset.range 324, stT267 (i+1)) + stT267 325 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 324
    simpa using h
  have hprev := st267_p324
  have hstep := st267_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p326 : ((361109730241/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT267 (i+1))
      = (∑ i ∈ Finset.range 325, stT267 (i+1)) + stT267 326 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 325
    simpa using h
  have hprev := st267_p325
  have hstep := st267_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p327 : ((744277011369/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT267 (i+1))
      = (∑ i ∈ Finset.range 326, stT267 (i+1)) + stT267 327 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 326
    simpa using h
  have hprev := st267_p326
  have hstep := st267_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p328 : ((112893896417/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT267 (i+1))
      = (∑ i ∈ Finset.range 327, stT267 (i+1)) + stT267 328 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 327
    simpa using h
  have hprev := st267_p327
  have hstep := st267_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p329 : ((838484050867/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT267 (i+1))
      = (∑ i ∈ Finset.range 328, stT267 (i+1)) + stT267 329 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 328
    simpa using h
  have hprev := st267_p328
  have hstep := st267_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p330 : ((24855648989/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT267 (i+1))
      = (∑ i ∈ Finset.range 329, stT267 (i+1)) + stT267 330 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 329
    simpa using h
  have hprev := st267_p329
  have hstep := st267_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p331 : ((60484659483/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT267 (i+1))
      = (∑ i ∈ Finset.range 330, stT267 (i+1)) + stT267 331 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 330
    simpa using h
  have hprev := st267_p330
  have hstep := st267_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p332 : ((6311431883987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT267 (i+1))
      = (∑ i ∈ Finset.range 331, stT267 (i+1)) + stT267 332 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 331
    simpa using h
  have hprev := st267_p331
  have hstep := st267_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p333 : ((1367966090207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT267 (i+1))
      = (∑ i ∈ Finset.range 332, stT267 (i+1)) + stT267 333 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 332
    simpa using h
  have hprev := st267_p332
  have hstep := st267_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p334 : ((182780091419/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT267 (i+1))
      = (∑ i ∈ Finset.range 333, stT267 (i+1)) + stT267 334 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 333
    simpa using h
  have hprev := st267_p333
  have hstep := st267_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p335 : ((3720530739921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT267 (i+1))
      = (∑ i ∈ Finset.range 334, stT267 (i+1)) + stT267 335 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 334
    simpa using h
  have hprev := st267_p334
  have hstep := st267_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p336 : ((7153195386327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT267 (i+1))
      = (∑ i ∈ Finset.range 335, stT267 (i+1)) + stT267 336 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 335
    simpa using h
  have hprev := st267_p335
  have hstep := st267_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p337 : ((6621745383507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT267 (i+1))
      = (∑ i ∈ Finset.range 336, stT267 (i+1)) + stT267 337 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 336
    simpa using h
  have hprev := st267_p336
  have hstep := st267_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p338 : ((1232730981371/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT267 (i+1))
      = (∑ i ∈ Finset.range 337, stT267 (i+1)) + stT267 338 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 337
    simpa using h
  have hprev := st267_p337
  have hstep := st267_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p339 : ((6049113435337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT267 (i+1))
      = (∑ i ∈ Finset.range 338, stT267 (i+1)) + stT267 339 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 338
    simpa using h
  have hprev := st267_p338
  have hstep := st267_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p340 : ((6343572048667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT267 (i+1))
      = (∑ i ∈ Finset.range 339, stT267 (i+1)) + stT267 340 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 339
    simpa using h
  have hprev := st267_p339
  have hstep := st267_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p341 : ((6872875925857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT267 (i+1))
      = (∑ i ∈ Finset.range 340, stT267 (i+1)) + stT267 341 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 340
    simpa using h
  have hprev := st267_p340
  have hstep := st267_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p342 : ((7328330891449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT267 (i+1))
      = (∑ i ∈ Finset.range 341, stT267 (i+1)) + stT267 342 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 341
    simpa using h
  have hprev := st267_p341
  have hstep := st267_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p343 : ((7447211462779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT267 (i+1))
      = (∑ i ∈ Finset.range 342, stT267 (i+1)) + stT267 343 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 342
    simpa using h
  have hprev := st267_p342
  have hstep := st267_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p344 : ((7162960427831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT267 (i+1))
      = (∑ i ∈ Finset.range 343, stT267 (i+1)) + stT267 344 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 343
    simpa using h
  have hprev := st267_p343
  have hstep := st267_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p345 : ((6640046142691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT267 (i+1))
      = (∑ i ∈ Finset.range 344, stT267 (i+1)) + stT267 345 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 344
    simpa using h
  have hprev := st267_p344
  have hstep := st267_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p346 : ((6176791700683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT267 (i+1))
      = (∑ i ∈ Finset.range 345, stT267 (i+1)) + stT267 346 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 345
    simpa using h
  have hprev := st267_p345
  have hstep := st267_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p347 : ((3017317275011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT267 (i+1))
      = (∑ i ∈ Finset.range 346, stT267 (i+1)) + stT267 347 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 346
    simpa using h
  have hprev := st267_p346
  have hstep := st267_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p348 : ((3145895399143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT267 (i+1))
      = (∑ i ∈ Finset.range 347, stT267 (i+1)) + stT267 348 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 347
    simpa using h
  have hprev := st267_p347
  have hstep := st267_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p349 : ((6802466907887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT267 (i+1))
      = (∑ i ∈ Finset.range 348, stT267 (i+1)) + stT267 349 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 348
    simpa using h
  have hprev := st267_p348
  have hstep := st267_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p350 : ((1456294583689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT267 (i+1))
      = (∑ i ∈ Finset.range 349, stT267 (i+1)) + stT267 350 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 349
    simpa using h
  have hprev := st267_p349
  have hstep := st267_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p351 : ((1492826719369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT267 (i+1))
      = (∑ i ∈ Finset.range 350, stT267 (i+1)) + stT267 351 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 350
    simpa using h
  have hprev := st267_p350
  have hstep := st267_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p352 : ((1450303819809/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT267 (i+1))
      = (∑ i ∈ Finset.range 351, stT267 (i+1)) + stT267 352 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 351
    simpa using h
  have hprev := st267_p351
  have hstep := st267_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p353 : ((6761901890263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT267 (i+1))
      = (∑ i ∈ Finset.range 352, stT267 (i+1)) + stT267 353 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 352
    simpa using h
  have hprev := st267_p352
  have hstep := st267_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p354 : ((6263011982533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT267 (i+1))
      = (∑ i ∈ Finset.range 353, stT267 (i+1)) + stT267 354 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 353
    simpa using h
  have hprev := st267_p353
  have hstep := st267_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p355 : ((6024793458223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT267 (i+1))
      = (∑ i ∈ Finset.range 354, stT267 (i+1)) + stT267 355 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 354
    simpa using h
  have hprev := st267_p354
  have hstep := st267_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p356 : ((6174116684737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT267 (i+1))
      = (∑ i ∈ Finset.range 355, stT267 (i+1)) + stT267 356 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 355
    simpa using h
  have hprev := st267_p355
  have hstep := st267_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p357 : ((6629068847129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT267 (i+1))
      = (∑ i ∈ Finset.range 356, stT267 (i+1)) + stT267 357 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 356
    simpa using h
  have hprev := st267_p356
  have hstep := st267_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p358 : ((7145875046633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT267 (i+1))
      = (∑ i ∈ Finset.range 357, stT267 (i+1)) + stT267 358 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 357
    simpa using h
  have hprev := st267_p357
  have hstep := st267_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p359 : ((23282862333/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT267 (i+1))
      = (∑ i ∈ Finset.range 358, stT267 (i+1)) + stT267 359 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 358
    simpa using h
  have hprev := st267_p358
  have hstep := st267_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p360 : ((7383556206351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT267 (i+1))
      = (∑ i ∈ Finset.range 359, stT267 (i+1)) + stT267 360 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 359
    simpa using h
  have hprev := st267_p359
  have hstep := st267_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p361 : ((6981940256231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT267 (i+1))
      = (∑ i ∈ Finset.range 360, stT267 (i+1)) + stT267 361 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 360
    simpa using h
  have hprev := st267_p360
  have hstep := st267_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p362 : ((6456661353741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT267 (i+1))
      = (∑ i ∈ Finset.range 361, stT267 (i+1)) + stT267 362 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 361
    simpa using h
  have hprev := st267_p361
  have hstep := st267_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p363 : ((6080680275981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT267 (i+1))
      = (∑ i ∈ Finset.range 362, stT267 (i+1)) + stT267 363 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 362
    simpa using h
  have hprev := st267_p362
  have hstep := st267_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p364 : ((3023577782779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT267 (i+1))
      = (∑ i ∈ Finset.range 363, stT267 (i+1)) + stT267 364 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 363
    simpa using h
  have hprev := st267_p363
  have hstep := st267_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p365 : ((796447035187/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT267 (i+1))
      = (∑ i ∈ Finset.range 364, stT267 (i+1)) + stT267 365 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 364
    simpa using h
  have hprev := st267_p364
  have hstep := st267_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p366 : ((1721642408531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT267 (i+1))
      = (∑ i ∈ Finset.range 365, stT267 (i+1)) + stT267 366 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 365
    simpa using h
  have hprev := st267_p365
  have hstep := st267_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p367 : ((7329695887579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT267 (i+1))
      = (∑ i ∈ Finset.range 366, stT267 (i+1)) + stT267 367 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 366
    simpa using h
  have hprev := st267_p366
  have hstep := st267_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p368 : ((7477472649289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT267 (i+1))
      = (∑ i ∈ Finset.range 367, stT267 (i+1)) + stT267 368 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 367
    simpa using h
  have hprev := st267_p367
  have hstep := st267_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p369 : ((7257087188609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT267 (i+1))
      = (∑ i ∈ Finset.range 368, stT267 (i+1)) + stT267 369 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 368
    simpa using h
  have hprev := st267_p368
  have hstep := st267_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p370 : ((1356100356601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT267 (i+1))
      = (∑ i ∈ Finset.range 369, stT267 (i+1)) + stT267 370 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 369
    simpa using h
  have hprev := st267_p369
  have hstep := st267_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p371 : ((1257194611721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT267 (i+1))
      = (∑ i ∈ Finset.range 370, stT267 (i+1)) + stT267 371 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 370
    simpa using h
  have hprev := st267_p370
  have hstep := st267_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p372 : ((240729696869/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT267 (i+1))
      = (∑ i ∈ Finset.range 371, stT267 (i+1)) + stT267 372 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 371
    simpa using h
  have hprev := st267_p371
  have hstep := st267_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p373 : ((1221594532033/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT267 (i+1))
      = (∑ i ∈ Finset.range 372, stT267 (i+1)) + stT267 373 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 372
    simpa using h
  have hprev := st267_p372
  have hstep := st267_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p374 : ((6509456587923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT267 (i+1))
      = (∑ i ∈ Finset.range 373, stT267 (i+1)) + stT267 374 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 373
    simpa using h
  have hprev := st267_p373
  have hstep := st267_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p375 : ((7025575766337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT267 (i+1))
      = (∑ i ∈ Finset.range 374, stT267 (i+1)) + stT267 375 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 374
    simpa using h
  have hprev := st267_p374
  have hstep := st267_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p376 : ((7405588541167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT267 (i+1))
      = (∑ i ∈ Finset.range 375, stT267 (i+1)) + stT267 376 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 375
    simpa using h
  have hprev := st267_p375
  have hstep := st267_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p377 : ((7466887965739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT267 (i+1))
      = (∑ i ∈ Finset.range 376, stT267 (i+1)) + stT267 377 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 376
    simpa using h
  have hprev := st267_p376
  have hstep := st267_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p378 : ((7181586966379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT267 (i+1))
      = (∑ i ∈ Finset.range 377, stT267 (i+1)) + stT267 378 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 377
    simpa using h
  have hprev := st267_p377
  have hstep := st267_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p379 : ((6687536329921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT267 (i+1))
      = (∑ i ∈ Finset.range 378, stT267 (i+1)) + stT267 379 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 378
    simpa using h
  have hprev := st267_p378
  have hstep := st267_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p380 : ((6220393272201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT267 (i+1))
      = (∑ i ∈ Finset.range 379, stT267 (i+1)) + stT267 380 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 379
    simpa using h
  have hprev := st267_p379
  have hstep := st267_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p381 : ((1200154627401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT267 (i+1))
      = (∑ i ∈ Finset.range 380, stT267 (i+1)) + stT267 381 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 380
    simpa using h
  have hprev := st267_p380
  have hstep := st267_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p382 : ((6130753225341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT267 (i+1))
      = (∑ i ∈ Finset.range 381, stT267 (i+1)) + stT267 382 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 381
    simpa using h
  have hprev := st267_p381
  have hstep := st267_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p383 : ((6547823078013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT267 (i+1))
      = (∑ i ∈ Finset.range 382, stT267 (i+1)) + stT267 383 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 382
    simpa using h
  have hprev := st267_p382
  have hstep := st267_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p384 : ((7056460792143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT267 (i+1))
      = (∑ i ∈ Finset.range 383, stT267 (i+1)) + stT267 384 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 383
    simpa using h
  have hprev := st267_p383
  have hstep := st267_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p385 : ((3710309176703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT267 (i+1))
      = (∑ i ∈ Finset.range 384, stT267 (i+1)) + stT267 385 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 384
    simpa using h
  have hprev := st267_p384
  have hstep := st267_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p386 : ((23353562843/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT267 (i+1))
      = (∑ i ∈ Finset.range 385, stT267 (i+1)) + stT267 386 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 385
    simpa using h
  have hprev := st267_p385
  have hstep := st267_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p387 : ((7191405369787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT267 (i+1))
      = (∑ i ∈ Finset.range 386, stT267 (i+1)) + stT267 387 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 386
    simpa using h
  have hprev := st267_p386
  have hstep := st267_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p388 : ((6705542567849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT267 (i+1))
      = (∑ i ∈ Finset.range 387, stT267 (i+1)) + stT267 388 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 387
    simpa using h
  have hprev := st267_p387
  have hstep := st267_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p389 : ((3118564340947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT267 (i+1))
      = (∑ i ∈ Finset.range 388, stT267 (i+1)) + stT267 389 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 388
    simpa using h
  have hprev := st267_p388
  have hstep := st267_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p390 : ((2998858979317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT267 (i+1))
      = (∑ i ∈ Finset.range 389, stT267 (i+1)) + stT267 390 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 389
    simpa using h
  have hprev := st267_p389
  have hstep := st267_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p391 : ((3046930794693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT267 (i+1))
      = (∑ i ∈ Finset.range 390, stT267 (i+1)) + stT267 391 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 390
    simpa using h
  have hprev := st267_p390
  have hstep := st267_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p392 : ((648096143223/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT267 (i+1))
      = (∑ i ∈ Finset.range 391, stT267 (i+1)) + stT267 392 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 391
    simpa using h
  have hprev := st267_p391
  have hstep := st267_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p393 : ((54572613707/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT267 (i+1))
      = (∑ i ∈ Finset.range 392, stT267 (i+1)) + stT267 393 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 392
    simpa using h
  have hprev := st267_p392
  have hstep := st267_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p394 : ((461428340427/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT267 (i+1))
      = (∑ i ∈ Finset.range 393, stT267 (i+1)) + stT267 394 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 393
    simpa using h
  have hprev := st267_p393
  have hstep := st267_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p395 : ((74988515763/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT267 (i+1))
      = (∑ i ∈ Finset.range 394, stT267 (i+1)) + stT267 395 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 394
    simpa using h
  have hprev := st267_p394
  have hstep := st267_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p396 : ((7283682488361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT267 (i+1))
      = (∑ i ∈ Finset.range 395, stT267 (i+1)) + stT267 396 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 395
    simpa using h
  have hprev := st267_p395
  have hstep := st267_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p397 : ((1366566554763/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT267 (i+1))
      = (∑ i ∈ Finset.range 396, stT267 (i+1)) + stT267 397 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 396
    simpa using h
  have hprev := st267_p396
  have hstep := st267_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p398 : ((253731122721/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT267 (i+1))
      = (∑ i ∈ Finset.range 397, stT267 (i+1)) + stT267 398 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 397
    simpa using h
  have hprev := st267_p397
  have hstep := st267_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p399 : ((241075272161/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT267 (i+1))
      = (∑ i ∈ Finset.range 398, stT267 (i+1)) + stT267 399 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 398
    simpa using h
  have hprev := st267_p398
  have hstep := st267_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p400 : ((1504746822059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT267 (i+1))
      = (∑ i ∈ Finset.range 399, stT267 (i+1)) + stT267 400 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 399
    simpa using h
  have hprev := st267_p399
  have hstep := st267_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p401 : ((316077435987/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT267 (i+1))
      = (∑ i ∈ Finset.range 400, stT267 (i+1)) + stT267 401 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 400
    simpa using h
  have hprev := st267_p400
  have hstep := st267_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p402 : ((680416553407/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT267 (i+1))
      = (∑ i ∈ Finset.range 401, stT267 (i+1)) + stT267 402 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 401
    simpa using h
  have hprev := st267_p401
  have hstep := st267_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p403 : ((726129007579/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT267 (i+1))
      = (∑ i ∈ Finset.range 402, stT267 (i+1)) + stT267 403 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 402
    simpa using h
  have hprev := st267_p402
  have hstep := st267_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p404 : ((234376576767/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT267 (i+1))
      = (∑ i ∈ Finset.range 403, stT267 (i+1)) + stT267 404 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 403
    simpa using h
  have hprev := st267_p403
  have hstep := st267_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p405 : ((185527918981/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT267 (i+1))
      = (∑ i ∈ Finset.range 404, stT267 (i+1)) + stT267 405 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 404
    simpa using h
  have hprev := st267_p404
  have hstep := st267_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p406 : ((110295840251/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT267 (i+1))
      = (∑ i ∈ Finset.range 405, stT267 (i+1)) + stT267 406 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 405
    simpa using h
  have hprev := st267_p405
  have hstep := st267_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p407 : ((3282755795151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT267 (i+1))
      = (∑ i ∈ Finset.range 406, stT267 (i+1)) + stT267 407 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 406
    simpa using h
  have hprev := st267_p406
  have hstep := st267_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p408 : ((122916271939/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT267 (i+1))
      = (∑ i ∈ Finset.range 407, stT267 (i+1)) + stT267 408 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 407
    simpa using h
  have hprev := st267_p407
  have hstep := st267_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p409 : ((1194503903773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT267 (i+1))
      = (∑ i ∈ Finset.range 408, stT267 (i+1)) + stT267 409 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 408
    simpa using h
  have hprev := st267_p408
  have hstep := st267_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p410 : ((6115608217177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT267 (i+1))
      = (∑ i ∈ Finset.range 409, stT267 (i+1)) + stT267 410 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 409
    simpa using h
  have hprev := st267_p409
  have hstep := st267_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p411 : ((6515209452211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT267 (i+1))
      = (∑ i ∈ Finset.range 410, stT267 (i+1)) + stT267 411 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 410
    simpa using h
  have hprev := st267_p410
  have hstep := st267_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p412 : ((7007724175019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT267 (i+1))
      = (∑ i ∈ Finset.range 411, stT267 (i+1)) + stT267 412 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 411
    simpa using h
  have hprev := st267_p411
  have hstep := st267_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p413 : ((739347173453/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT267 (i+1))
      = (∑ i ∈ Finset.range 412, stT267 (i+1)) + stT267 413 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 412
    simpa using h
  have hprev := st267_p412
  have hstep := st267_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p414 : ((7517581936801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT267 (i+1))
      = (∑ i ∈ Finset.range 413, stT267 (i+1)) + stT267 414 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 413
    simpa using h
  have hprev := st267_p413
  have hstep := st267_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p415 : ((7331465387413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT267 (i+1))
      = (∑ i ∈ Finset.range 414, stT267 (i+1)) + stT267 415 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 414
    simpa using h
  have hprev := st267_p414
  have hstep := st267_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p416 : ((6910759427879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT267 (i+1))
      = (∑ i ∈ Finset.range 415, stT267 (i+1)) + stT267 416 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 415
    simpa using h
  have hprev := st267_p415
  have hstep := st267_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p417 : ((1605890314681/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT267 (i+1))
      = (∑ i ∈ Finset.range 416, stT267 (i+1)) + stT267 417 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 416
    simpa using h
  have hprev := st267_p416
  have hstep := st267_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p418 : ((1515683873591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT267 (i+1))
      = (∑ i ∈ Finset.range 417, stT267 (i+1)) + stT267 418 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 417
    simpa using h
  have hprev := st267_p417
  have hstep := st267_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p419 : ((746209928809/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT267 (i+1))
      = (∑ i ∈ Finset.range 418, stT267 (i+1)) + stT267 419 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 418
    simpa using h
  have hprev := st267_p418
  have hstep := st267_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p420 : ((1544910346943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT267 (i+1))
      = (∑ i ∈ Finset.range 419, stT267 (i+1)) + stT267 420 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 419
    simpa using h
  have hprev := st267_p419
  have hstep := st267_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p421 : ((413088557837/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT267 (i+1))
      = (∑ i ∈ Finset.range 420, stT267 (i+1)) + stT267 421 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 420
    simpa using h
  have hprev := st267_p420
  have hstep := st267_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p422 : ((443203214729/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT267 (i+1))
      = (∑ i ∈ Finset.range 421, stT267 (i+1)) + stT267 422 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 421
    simpa using h
  have hprev := st267_p421
  have hstep := st267_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p423 : ((929848309633/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT267 (i+1))
      = (∑ i ∈ Finset.range 422, stT267 (i+1)) + stT267 423 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 422
    simpa using h
  have hprev := st267_p422
  have hstep := st267_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p424 : ((939870503587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT267 (i+1))
      = (∑ i ∈ Finset.range 423, stT267 (i+1)) + stT267 424 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 423
    simpa using h
  have hprev := st267_p423
  have hstep := st267_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p425 : ((36511307541/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT267 (i+1))
      = (∑ i ∈ Finset.range 424, stT267 (i+1)) + stT267 425 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 424
    simpa using h
  have hprev := st267_p424
  have hstep := st267_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p426 : ((5369169769/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT267 (i+1))
      = (∑ i ∈ Finset.range 425, stT267 (i+1)) + stT267 426 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 425
    simpa using h
  have hprev := st267_p425
  have hstep := st267_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p427 : ((3196857065647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT267 (i+1))
      = (∑ i ∈ Finset.range 426, stT267 (i+1)) + stT267 427 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 426
    simpa using h
  have hprev := st267_p426
  have hstep := st267_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p428 : ((6046791015983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT267 (i+1))
      = (∑ i ∈ Finset.range 427, stT267 (i+1)) + stT267 428 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 427
    simpa using h
  have hprev := st267_p427
  have hstep := st267_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p429 : ((1490400380537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT267 (i+1))
      = (∑ i ∈ Finset.range 428, stT267 (i+1)) + stT267 429 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 428
    simpa using h
  have hprev := st267_p428
  have hstep := st267_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p430 : ((3084435772479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT267 (i+1))
      = (∑ i ∈ Finset.range 429, stT267 (i+1)) + stT267 430 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 429
    simpa using h
  have hprev := st267_p429
  have hstep := st267_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p431 : ((1647526554639/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT267 (i+1))
      = (∑ i ∈ Finset.range 430, stT267 (i+1)) + stT267 431 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 430
    simpa using h
  have hprev := st267_p430
  have hstep := st267_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p432 : ((7068165971181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT267 (i+1))
      = (∑ i ∈ Finset.range 431, stT267 (i+1)) + stT267 432 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 431
    simpa using h
  have hprev := st267_p431
  have hstep := st267_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p433 : ((1856574260767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT267 (i+1))
      = (∑ i ∈ Finset.range 432, stT267 (i+1)) + stT267 433 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 432
    simpa using h
  have hprev := st267_p432
  have hstep := st267_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p434 : ((470836294333/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT267 (i+1))
      = (∑ i ∈ Finset.range 433, stT267 (i+1)) + stT267 434 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 433
    simpa using h
  have hprev := st267_p433
  have hstep := st267_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p435 : ((918912971983/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT267 (i+1))
      = (∑ i ∈ Finset.range 434, stT267 (i+1)) + stT267 435 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 434
    simpa using h
  have hprev := st267_p434
  have hstep := st267_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p436 : ((434226697829/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT267 (i+1))
      = (∑ i ∈ Finset.range 435, stT267 (i+1)) + stT267 436 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 435
    simpa using h
  have hprev := st267_p435
  have hstep := st267_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p437 : ((6469689345209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT267 (i+1))
      = (∑ i ∈ Finset.range 436, stT267 (i+1)) + stT267 437 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 436
    simpa using h
  have hprev := st267_p436
  have hstep := st267_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p438 : ((6090366042593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT267 (i+1))
      = (∑ i ∈ Finset.range 437, stT267 (i+1)) + stT267 438 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 437
    simpa using h
  have hprev := st267_p437
  have hstep := st267_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p439 : ((5945581156501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT267 (i+1))
      = (∑ i ∈ Finset.range 438, stT267 (i+1)) + stT267 439 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 438
    simpa using h
  have hprev := st267_p438
  have hstep := st267_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p440 : ((3043070977367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT267 (i+1))
      = (∑ i ∈ Finset.range 439, stT267 (i+1)) + stT267 440 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 439
    simpa using h
  have hprev := st267_p439
  have hstep := st267_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p441 : ((807592637993/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT267 (i+1))
      = (∑ i ∈ Finset.range 440, stT267 (i+1)) + stT267 441 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 440
    simpa using h
  have hprev := st267_p440
  have hstep := st267_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p442 : ((6935495501809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT267 (i+1))
      = (∑ i ∈ Finset.range 441, stT267 (i+1)) + stT267 442 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 441
    simpa using h
  have hprev := st267_p441
  have hstep := st267_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p443 : ((7342292859749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT267 (i+1))
      = (∑ i ∈ Finset.range 442, stT267 (i+1)) + stT267 443 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 442
    simpa using h
  have hprev := st267_p442
  have hstep := st267_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p444 : ((7538359540091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT267 (i+1))
      = (∑ i ∈ Finset.range 443, stT267 (i+1)) + stT267 444 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 443
    simpa using h
  have hprev := st267_p443
  have hstep := st267_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p445 : ((7455932895657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT267 (i+1))
      = (∑ i ∈ Finset.range 444, stT267 (i+1)) + stT267 445 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 444
    simpa using h
  have hprev := st267_p444
  have hstep := st267_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p446 : ((284996197617/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT267 (i+1))
      = (∑ i ∈ Finset.range 445, stT267 (i+1)) + stT267 446 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 445
    simpa using h
  have hprev := st267_p445
  have hstep := st267_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p447 : ((1332242069237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT267 (i+1))
      = (∑ i ∈ Finset.range 446, stT267 (i+1)) + stT267 447 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 446
    simpa using h
  have hprev := st267_p446
  have hstep := st267_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p448 : ((6225639458561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT267 (i+1))
      = (∑ i ∈ Finset.range 447, stT267 (i+1)) + stT267 448 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 447
    simpa using h
  have hprev := st267_p447
  have hstep := st267_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p449 : ((5967935003111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT267 (i+1))
      = (∑ i ∈ Finset.range 448, stT267 (i+1)) + stT267 449 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 448
    simpa using h
  have hprev := st267_p448
  have hstep := st267_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p450 : ((5975639630087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT267 (i+1))
      = (∑ i ∈ Finset.range 449, stT267 (i+1)) + stT267 450 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 449
    simpa using h
  have hprev := st267_p449
  have hstep := st267_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p451 : ((780626771169/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT267 (i+1))
      = (∑ i ∈ Finset.range 450, stT267 (i+1)) + stT267 451 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 450
    simpa using h
  have hprev := st267_p450
  have hstep := st267_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p452 : ((835432295239/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT267 (i+1))
      = (∑ i ∈ Finset.range 451, stT267 (i+1)) + stT267 452 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 451
    simpa using h
  have hprev := st267_p451
  have hstep := st267_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p453 : ((892747548269/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT267 (i+1))
      = (∑ i ∈ Finset.range 452, stT267 (i+1)) + stT267 453 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 452
    simpa using h
  have hprev := st267_p452
  have hstep := st267_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p454 : ((37330417931/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT267 (i+1))
      = (∑ i ∈ Finset.range 453, stT267 (i+1)) + stT267 454 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 453
    simpa using h
  have hprev := st267_p453
  have hstep := st267_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p455 : ((3773812531469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT267 (i+1))
      = (∑ i ∈ Finset.range 454, stT267 (i+1)) + stT267 455 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 454
    simpa using h
  have hprev := st267_p454
  have hstep := st267_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p456 : ((7360378575181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT267 (i+1))
      = (∑ i ∈ Finset.range 455, stT267 (i+1)) + stT267 456 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 455
    simpa using h
  have hprev := st267_p455
  have hstep := st267_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p457 : ((174192600619/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT267 (i+1))
      = (∑ i ∈ Finset.range 456, stT267 (i+1)) + stT267 457 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 456
    simpa using h
  have hprev := st267_p456
  have hstep := st267_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p458 : ((325021467603/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT267 (i+1))
      = (∑ i ∈ Finset.range 457, stT267 (i+1)) + stT267 458 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 457
    simpa using h
  have hprev := st267_p457
  have hstep := st267_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p459 : ((382056256143/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT267 (i+1))
      = (∑ i ∈ Finset.range 458, stT267 (i+1)) + stT267 459 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 458
    simpa using h
  have hprev := st267_p458
  have hstep := st267_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p460 : ((4634364433/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT267 (i+1))
      = (∑ i ∈ Finset.range 459, stT267 (i+1)) + stT267 460 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 459
    simpa using h
  have hprev := st267_p459
  have hstep := st267_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p461 : ((300799188267/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT267 (i+1))
      = (∑ i ∈ Finset.range 460, stT267 (i+1)) + stT267 461 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 460
    simpa using h
  have hprev := st267_p460
  have hstep := st267_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p462 : ((316822587989/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT267 (i+1))
      = (∑ i ∈ Finset.range 461, stT267 (i+1)) + stT267 462 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 461
    simpa using h
  have hprev := st267_p461
  have hstep := st267_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p463 : ((6788549394241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT267 (i+1))
      = (∑ i ∈ Finset.range 462, stT267 (i+1)) + stT267 463 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 462
    simpa using h
  have hprev := st267_p462
  have hstep := st267_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p464 : ((7225801239301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT267 (i+1))
      = (∑ i ∈ Finset.range 463, stT267 (i+1)) + stT267 464 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 463
    simpa using h
  have hprev := st267_p463
  have hstep := st267_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p465 : ((1501541792143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT267 (i+1))
      = (∑ i ∈ Finset.range 464, stT267 (i+1)) + stT267 465 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 464
    simpa using h
  have hprev := st267_p464
  have hstep := st267_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p466 : ((754466401149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT267 (i+1))
      = (∑ i ∈ Finset.range 465, stT267 (i+1)) + stT267 466 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 465
    simpa using h
  have hprev := st267_p465
  have hstep := st267_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p467 : ((732586892059/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT267 (i+1))
      = (∑ i ∈ Finset.range 466, stT267 (i+1)) + stT267 467 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 466
    simpa using h
  have hprev := st267_p466
  have hstep := st267_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p468 : ((6921800067207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT267 (i+1))
      = (∑ i ∈ Finset.range 467, stT267 (i+1)) + stT267 468 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 467
    simpa using h
  have hprev := st267_p467
  have hstep := st267_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p469 : ((6460924948503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT267 (i+1))
      = (∑ i ∈ Finset.range 468, stT267 (i+1)) + stT267 469 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 468
    simpa using h
  have hprev := st267_p468
  have hstep := st267_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p470 : ((6088551364427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT267 (i+1))
      = (∑ i ∈ Finset.range 469, stT267 (i+1)) + stT267 470 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 469
    simpa using h
  have hprev := st267_p469
  have hstep := st267_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p471 : ((5921057906099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT267 (i+1))
      = (∑ i ∈ Finset.range 470, stT267 (i+1)) + stT267 471 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 470
    simpa using h
  have hprev := st267_p470
  have hstep := st267_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p472 : ((1201982157601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT267 (i+1))
      = (∑ i ∈ Finset.range 471, stT267 (i+1)) + stT267 472 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 471
    simpa using h
  have hprev := st267_p471
  have hstep := st267_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p473 : ((1265289904521/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT267 (i+1))
      = (∑ i ∈ Finset.range 472, stT267 (i+1)) + stT267 473 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 472
    simpa using h
  have hprev := st267_p472
  have hstep := st267_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p474 : ((338587242543/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT267 (i+1))
      = (∑ i ∈ Finset.range 473, stT267 (i+1)) + stT267 474 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 473
    simpa using h
  have hprev := st267_p473
  have hstep := st267_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p475 : ((1441589720019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT267 (i+1))
      = (∑ i ∈ Finset.range 474, stT267 (i+1)) + stT267 475 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 474
    simpa using h
  have hprev := st267_p474
  have hstep := st267_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p476 : ((7501127871153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT267 (i+1))
      = (∑ i ∈ Finset.range 475, stT267 (i+1)) + stT267 476 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 475
    simpa using h
  have hprev := st267_p475
  have hstep := st267_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p477 : ((7562172206517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT267 (i+1))
      = (∑ i ∈ Finset.range 476, stT267 (i+1)) + stT267 477 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 476
    simpa using h
  have hprev := st267_p476
  have hstep := st267_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p478 : ((7373388600527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT267 (i+1))
      = (∑ i ∈ Finset.range 477, stT267 (i+1)) + stT267 478 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 477
    simpa using h
  have hprev := st267_p477
  have hstep := st267_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p479 : ((6993042715103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT267 (i+1))
      = (∑ i ∈ Finset.range 478, stT267 (i+1)) + stT267 479 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 478
    simpa using h
  have hprev := st267_p478
  have hstep := st267_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p480 : ((1307359409783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT267 (i+1))
      = (∑ i ∈ Finset.range 479, stT267 (i+1)) + stT267 480 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 479
    simpa using h
  have hprev := st267_p479
  have hstep := st267_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p481 : ((6142242140629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT267 (i+1))
      = (∑ i ∈ Finset.range 480, stT267 (i+1)) + stT267 481 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 480
    simpa using h
  have hprev := st267_p480
  have hstep := st267_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p482 : ((5927385262613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT267 (i+1))
      = (∑ i ∈ Finset.range 481, stT267 (i+1)) + stT267 482 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 481
    simpa using h
  have hprev := st267_p481
  have hstep := st267_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p483 : ((2977820619549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT267 (i+1))
      = (∑ i ∈ Finset.range 482, stT267 (i+1)) + stT267 483 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 482
    simpa using h
  have hprev := st267_p482
  have hstep := st267_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p484 : ((6217658704353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT267 (i+1))
      = (∑ i ∈ Finset.range 483, stT267 (i+1)) + stT267 484 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 483
    simpa using h
  have hprev := st267_p483
  have hstep := st267_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p485 : ((6634922763033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT267 (i+1))
      = (∑ i ∈ Finset.range 484, stT267 (i+1)) + stT267 485 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 484
    simpa using h
  have hprev := st267_p484
  have hstep := st267_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p486 : ((3541885568289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT267 (i+1))
      = (∑ i ∈ Finset.range 485, stT267 (i+1)) + stT267 486 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 485
    simpa using h
  have hprev := st267_p485
  have hstep := st267_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p487 : ((297289143503/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT267 (i+1))
      = (∑ i ∈ Finset.range 486, stT267 (i+1)) + stT267 487 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 486
    simpa using h
  have hprev := st267_p486
  have hstep := st267_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p488 : ((7578731937461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT267 (i+1))
      = (∑ i ∈ Finset.range 487, stT267 (i+1)) + stT267 488 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 487
    simpa using h
  have hprev := st267_p487
  have hstep := st267_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p489 : ((7481379781413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT267 (i+1))
      = (∑ i ∈ Finset.range 488, stT267 (i+1)) + stT267 489 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 488
    simpa using h
  have hprev := st267_p488
  have hstep := st267_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p490 : ((7169356004137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT267 (i+1))
      = (∑ i ∈ Finset.range 489, stT267 (i+1)) + stT267 490 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 489
    simpa using h
  have hprev := st267_p489
  have hstep := st267_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p491 : ((6733681740771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT267 (i+1))
      = (∑ i ∈ Finset.range 490, stT267 (i+1)) + stT267 491 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 490
    simpa using h
  have hprev := st267_p490
  have hstep := st267_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p492 : ((6300279628551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT267 (i+1))
      = (∑ i ∈ Finset.range 491, stT267 (i+1)) + stT267 492 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 491
    simpa using h
  have hprev := st267_p491
  have hstep := st267_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p493 : ((1198685437767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT267 (i+1))
      = (∑ i ∈ Finset.range 492, stT267 (i+1)) + stT267 493 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 492
    simpa using h
  have hprev := st267_p492
  have hstep := st267_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p494 : ((5900296034367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT267 (i+1))
      = (∑ i ∈ Finset.range 493, stT267 (i+1)) + stT267 494 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 493
    simpa using h
  have hprev := st267_p493
  have hstep := st267_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p495 : ((6046547776107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT267 (i+1))
      = (∑ i ∈ Finset.range 494, stT267 (i+1)) + stT267 495 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 494
    simpa using h
  have hprev := st267_p494
  have hstep := st267_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p496 : ((1277963283711/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT267 (i+1))
      = (∑ i ∈ Finset.range 495, stT267 (i+1)) + stT267 496 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 495
    simpa using h
  have hprev := st267_p495
  have hstep := st267_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p497 : ((6832431293939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT267 (i+1))
      = (∑ i ∈ Finset.range 496, stT267 (i+1)) + stT267 497 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 496
    simpa using h
  have hprev := st267_p496
  have hstep := st267_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p498 : ((7249546421459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT267 (i+1))
      = (∑ i ∈ Finset.range 497, stT267 (i+1)) + stT267 498 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 497
    simpa using h
  have hprev := st267_p497
  have hstep := st267_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p499 : ((1881105814407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT267 (i+1))
      = (∑ i ∈ Finset.range 498, stT267 (i+1)) + stT267 499 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 498
    simpa using h
  have hprev := st267_p498
  have hstep := st267_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_p500 : ((7580904917889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT267 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT267 (i+1))
      = (∑ i ∈ Finset.range 499, stT267 (i+1)) + stT267 500 := by
    have h := Finset.sum_range_succ (fun i => stT267 (i+1)) 499
    simpa using h
  have hprev := st267_p499
  have hstep := st267_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st267_s500 :
    |Real.sin (((267 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))
      - ((495993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1805139/5000000) (δ := 6703/500000000) (ψ := -904683/1000000) 267 264
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 267`** (evaluated boundary). -/
theorem station_267_sign : hardyG ((((267:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 267 500 (by norm_num) (by norm_num)
    ((-904683/1000000 : ℚ) : ℝ)
  have hchain := st267_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT267 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((267 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-904683/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st267_c500
  have hsinb := abs_le.mp st267_s500
  have hbdy_lo : ((-118483450770947/1425785000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((267 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ))) / 2
          - ((((267:ℕ)):ℝ))
            * Real.sin (((267 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-904683/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((267:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((267:ℝ) * Real.log (500:ℝ) - ((-904683/1000000 : ℚ) : ℝ))) / 2
        - ((267:ℝ)) * Real.sin ((267:ℝ) * Real.log (500:ℝ) - ((-904683/1000000 : ℚ) : ℝ))
        ≥ ((-529873621/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((267:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-529873621/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-529873621/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-529873621/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((267:ℕ)):ℝ))+1) * (((((267:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((4209864417883/7500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((7580904917889/10000000000000 : ℚ) : ℝ) + ((-118483450770947/1425785000000000 : ℚ) : ℝ)
      - ((4209864417883/7500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-904683/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((267:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-904683/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((267:ℕ)):ℝ)))).re
      - Real.sin ((-904683/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((267:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((267:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((267:ℕ)):ℝ))
      = (((((267:ℕ)):ℝ)) * (Real.log ((((267:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((267:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_267
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
  have hθwin : |(((-904683/1000000 : ℚ) : ℝ) + ((59:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((267:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((267:ℕ)):ℝ)))
    (φ := ((-904683/1000000 : ℚ) : ℝ) + ((59:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-904683/1000000 : ℚ) : ℝ) + ((59:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-904683/1000000 : ℚ)) : ℝ) - Real.pi) + ((59:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-904683/1000000 : ℚ)) : ℝ) - Real.pi) 59).1,
    (cos_sin_shift ((((-904683/1000000 : ℚ)) : ℝ) - Real.pi) 59).2]
  exact cos_sin_flip ((-904683/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_267_sign
end AxiomAudit
