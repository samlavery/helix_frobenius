import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 162` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT162 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((162 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))

theorem st162_c1 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((23357/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56963/625000) (δ := 201/1000000000) (ψ := -364563/1000000) 162 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t1 : ((93423/100000 : ℚ) : ℝ) ≤ stT162 1 := by
  have hc : ((93423/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93423/100000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((93423/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c2 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((451749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138417/1250000) (δ := 517/62500000) (ψ := -364563/1000000) 162 18
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t2 : ((798542667377/1250000000000 : ℚ) : ℝ) ≤ stT162 2 := by
  have hc : ((112931/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((798542667377/1250000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((112931/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c3 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-148897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6026397/10000000) (δ := 41/5000000) (ψ := -364563/1000000) 162 28
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t3 : ((-859715011221/2000000000000 : ℚ) : ℝ) ≤ stT162 3 := by
  have hc : ((-148907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-859715011221/2000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-148907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c4 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((314921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563029/5000000) (δ := 413/50000000) (ψ := -364563/1000000) 162 36
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t4 : ((314871/2000000 : ℚ) : ℝ) ≤ stT162 4 := by
  have hc : ((314871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((314871/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((314871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c5 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-942313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175017/250000) (δ := 8103/1000000000) (ψ := -364563/1000000) 162 42
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t5 : ((-526796937171/1250000000000 : ℚ) : ℝ) ≤ stT162 5 := by
  have hc : ((-942363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-526796937171/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-942363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c6 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-8067/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2003837/5000000) (δ := 8271/1000000000) (ψ := -364563/1000000) 162 46
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t6 : ((-65968842797/5000000000000 : ℚ) : ℝ) ≤ stT162 6 := by
  have hc : ((-16159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65968842797/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-16159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c7 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((25541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 721371/2000000) (δ := 51/6250000) (ψ := -364563/1000000) 162 50
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t7 : ((24124522741/500000000000 : ℚ) : ℝ) ≤ stT162 7 := by
  have hc : ((25531/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24124522741/500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((25531/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c8 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-468079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5144781/10000000) (δ := 8189/1000000000) (ψ := -364563/1000000) 162 54
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t8 : ((-827542997943/5000000000000 : ℚ) : ℝ) ≤ stT162 8 := by
  have hc : ((-468129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-827542997943/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-468129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c9 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-50609/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1141639/2500000) (δ := 8111/1000000000) (ψ := -364563/1000000) 162 57
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t9 : ((-84365016873/1000000000000 : ℚ) : ℝ) ≤ stT162 9 := by
  have hc : ((-50619/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84365016873/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-50619/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c10 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-89329/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 167213/250000) (δ := 13/1600000) (ψ := -364563/1000000) 162 59
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t10 : ((-70624735713/250000000000 : ℚ) : ℝ) ≤ stT162 10 := by
  have hc : ((-44667/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70624735713/250000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-44667/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c11 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((742571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1834739/10000000) (δ := 2039/250000000) (ψ := -364563/1000000) 162 62
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t11 : ((2238784719873/10000000000000 : ℚ) : ℝ) ≤ stT162 11 := by
  have hc : ((742521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2238784719873/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((742521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c12 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((69987/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248619/1250000) (δ := 8261/1000000000) (ψ := -364563/1000000) 162 64
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t12 : ((101010304241/500000000000 : ℚ) : ℝ) ≤ stT162 12 := by
  have hc : ((34991/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101010304241/500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((34991/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c13 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((91491/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2990319/10000000) (δ := 331/40000000) (ψ := -364563/1000000) 162 66
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t13 : ((1014862479/10000000000 : ℚ) : ℝ) ≤ stT162 13 := by
  have hc : ((182957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1014862479/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((182957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c14 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((402461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 397033/2500000) (δ := 8113/1000000000) (ψ := -364563/1000000) 162 68
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t14 : ((67222205177/312500000000 : ℚ) : ℝ) ≤ stT162 14 := by
  have hc : ((100609/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67222205177/312500000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((100609/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c15 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((728773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188567/1000000) (δ := 1013/125000000) (ψ := -364563/1000000) 162 70
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t15 : ((470388510331/2500000000000 : ℚ) : ℝ) ≤ stT162 15 := by
  have hc : ((728723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((470388510331/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((728723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c16 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-962101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -447719/625000) (δ := 4059/500000000) (ψ := -364563/1000000) 162 72
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t16 : ((-2405378462151/10000000000000 : ℚ) : ℝ) ≤ stT162 16 := by
  have hc : ((-962151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2405378462151/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-962151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c17 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((156441/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210187/1250000) (δ := 4113/500000000) (ψ := -364563/1000000) 162 73
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t17 : ((94850216109/500000000000 : ℚ) : ℝ) ≤ stT162 17 := by
  have hc : ((156431/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94850216109/500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((156431/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c18 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-873971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6585279/10000000) (δ := 8163/1000000000) (ψ := -364563/1000000) 162 75
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t18 : ((-2060087599483/10000000000000 : ℚ) : ℝ) ≤ stT162 18 := by
  have hc : ((-874021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2060087599483/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-874021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c19 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((987479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198013/5000000) (δ := 8147/1000000000) (ψ := -364563/1000000) 162 76
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t19 : ((2265317152353/10000000000000 : ℚ) : ℝ) ≤ stT162 19 := by
  have hc : ((987429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2265317152353/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((987429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c20 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-29277/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4669797/10000000) (δ := 8149/1000000000) (ψ := -364563/1000000) 162 77
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t20 : ((-8184567897/125000000000 : ℚ) : ℝ) ≤ stT162 20 := by
  have hc : ((-14641/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8184567897/125000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-14641/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c21 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-188069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3493049/5000000) (δ := 8269/1000000000) (ψ := -364563/1000000) 162 79
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t21 : ((-410422044141/2000000000000 : ℚ) : ℝ) ≤ stT162 21 := by
  have hc : ((-188079/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-410422044141/2000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-188079/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c22 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((29407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1926731/5000000) (δ := 8227/1000000000) (ψ := -364563/1000000) 162 80
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t22 : ((62589329499/10000000000000 : ℚ) : ℝ) ≤ stT162 22 := by
  have hc : ((29357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62589329499/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((29357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c23 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((811911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779223/5000000) (δ := 203/25000000) (ψ := -364563/1000000) 162 81
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t23 : ((211605886623/1250000000000 : ℚ) : ℝ) ≤ stT162 23 := by
  have hc : ((811861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211605886623/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((811861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c24 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((999929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29771/10000000) (δ := 819/100000000) (ψ := -364563/1000000) 162 82
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t24 : ((2040994009839/10000000000000 : ℚ) : ℝ) ≤ stT162 24 := by
  have hc : ((999879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2040994009839/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((999879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c25 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((949841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99397/1250000) (δ := 8297/1000000000) (ψ := -364563/1000000) 162 83
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t25 : ((949791/5000000 : ℚ) : ℝ) ≤ stT162 25 := by
  have hc : ((949791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((949791/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((949791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c26 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((462713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242899/2500000) (δ := 1641/200000000) (ψ := -364563/1000000) 162 84
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t26 : ((28356426899/156250000000 : ℚ) : ℝ) ≤ stT162 26 := by
  have hc : ((14459/15625 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28356426899/156250000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((14459/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c27 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((30501/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274227/5000000) (δ := 507/62500000) (ψ := -364563/1000000) 162 85
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t27 : ((1878277359/10000000000 : ℚ) : ℝ) ≤ stT162 27 := by
  have hc : ((487991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1878277359/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((487991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c28 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((246301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430591/10000000) (δ := 1023/125000000) (ψ := -364563/1000000) 162 86
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t28 : ((465441425647/2500000000000 : ℚ) : ℝ) ≤ stT162 28 := by
  have hc : ((492577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((465441425647/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((492577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c29 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((717471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -963289/5000000) (δ := 8277/1000000000) (ψ := -364563/1000000) 162 87
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t29 : ((1332217078213/10000000000000 : ℚ) : ℝ) ≤ stT162 29 := by
  have hc : ((717421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1332217078213/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((717421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c30 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((9023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3904433/10000000) (δ := 8233/1000000000) (ψ := -364563/1000000) 162 88
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t30 : ((16382373993/10000000000000 : ℚ) : ℝ) ≤ stT162 30 := by
  have hc : ((8973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16382373993/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((8973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c31 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-16409/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6332487/10000000) (δ := 407/50000000) (ψ := -364563/1000000) 162 89
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t31 : ((-1473662307/10000000000 : ℚ) : ℝ) ≤ stT162 31 := by
  have hc : ((-1641/2000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1473662307/10000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-1641/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c32 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-17243/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 815717/1250000) (δ := 8263/1000000000) (ψ := -364563/1000000) 162 89
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t32 : ((-7620843537/50000000000 : ℚ) : ℝ) ≤ stT162 32 := by
  have hc : ((-4311/5000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7620843537/50000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-4311/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c33 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((63953/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3280271/10000000) (δ := 1631/200000000) (ψ := -364563/1000000) 162 90
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t33 : ((27826521957/625000000000 : ℚ) : ℝ) ≤ stT162 33 := by
  have hc : ((127881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27826521957/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((127881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c34 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((247729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337227/10000000) (δ := 1631/200000000) (ψ := -364563/1000000) 162 91
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t34 : ((169932032701/1000000000000 : ℚ) : ℝ) ≤ stT162 34 := by
  have hc : ((495433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169932032701/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((495433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c35 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-18841/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4305253/10000000) (δ := 8141/1000000000) (ψ := -364563/1000000) 162 92
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t35 : ((-127430705201/5000000000000 : ℚ) : ℝ) ≤ stT162 35 := by
  have hc : ((-75389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127430705201/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-75389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c36 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-477667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3551981/5000000) (δ := 4131/500000000) (ψ := -364563/1000000) 162 92
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t36 : ((-199038373141/1250000000000 : ℚ) : ℝ) ≤ stT162 36 := by
  have hc : ((-119423/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199038373141/1250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-119423/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c37 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((542793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2492593/10000000) (δ := 4117/500000000) (ψ := -364563/1000000) 162 93
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t37 : ((892263521827/10000000000000 : ℚ) : ℝ) ≤ stT162 37 := by
  have hc : ((542743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((892263521827/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((542743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c38 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((568677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2414749/10000000) (δ := 8127/1000000000) (ψ := -364563/1000000) 162 94
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t38 : ((461217340089/5000000000000 : ℚ) : ℝ) ≤ stT162 38 := by
  have hc : ((568627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461217340089/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((568627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c39 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-19899/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1520527/2000000) (δ := 8219/1000000000) (ψ := -364563/1000000) 162 95
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t39 : ((-159327559/1000000000 : ℚ) : ℝ) ≤ stT162 39 := by
  have hc : ((-199/200 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159327559/1000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-199/200 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c40 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((488497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1325537/5000000) (δ := 8219/1000000000) (ψ := -364563/1000000) 162 95
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t40 : ((386151056343/5000000000000 : ℚ) : ℝ) ≤ stT162 40 := by
  have hc : ((488447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386151056343/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((488447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c41 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((170623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1528193/5000000) (δ := 507/62500000) (ψ := -364563/1000000) 162 96
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t41 : ((133214604363/2500000000000 : ℚ) : ℝ) ≤ stT162 41 := by
  have hc : ((85299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133214604363/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((85299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c42 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-895903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3351571/5000000) (δ := 507/62500000) (ψ := -364563/1000000) 162 96
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t42 : ((-691242970701/5000000000000 : ℚ) : ℝ) ≤ stT162 42 := by
  have hc : ((-895953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-691242970701/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-895953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c43 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((244507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 525031/10000000) (δ := 1641/200000000) (ψ := -364563/1000000) 162 97
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t43 : ((149140178033/1000000000000 : ℚ) : ℝ) ≤ stT162 43 := by
  have hc : ((488989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149140178033/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((488989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c44 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-87739/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1174437/2000000) (δ := 4149/500000000) (ψ := -364563/1000000) 162 98
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t44 : ((-529123863417/5000000000000 : ℚ) : ℝ) ≤ stT162 44 := by
  have hc : ((-350981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529123863417/5000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-350981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c45 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((68867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3229299/10000000) (δ := 4149/500000000) (ψ := -364563/1000000) 162 98
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t45 : ((205284321099/5000000000000 : ℚ) : ℝ) ≤ stT162 45 := by
  have hc : ((137709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205284321099/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((137709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c46 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((139457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3577209/10000000) (δ := 2053/250000000) (ψ := -364563/1000000) 162 99
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t46 : ((205544329533/10000000000000 : ℚ) : ℝ) ≤ stT162 46 := by
  have hc : ((139407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205544329533/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((139407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c47 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-231927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2566421/5000000) (δ := 8191/1000000000) (ψ := -364563/1000000) 162 99
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t47 : ((-422920981/6250000000 : ℚ) : ℝ) ≤ stT162 47 := by
  have hc : ((-14497/31250 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422920981/6250000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-14497/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c48 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((341331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1024247/5000000) (δ := 8119/1000000000) (ψ := -364563/1000000) 162 100
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t48 : ((1970530191/20000000000 : ℚ) : ℝ) ≤ stT162 48 := by
  have hc : ((170653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1970530191/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((170653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c49 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-813483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3151141/5000000) (δ := 8119/1000000000) (ψ := -364563/1000000) 162 100
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t49 : ((-290547616219/2500000000000 : ℚ) : ℝ) ≤ stT162 49 := by
  have hc : ((-813533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290547616219/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-813533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c50 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((441303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1223547/10000000) (δ := 8227/1000000000) (ψ := -364563/1000000) 162 101
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t50 : ((312030542107/2500000000000 : ℚ) : ℝ) ≤ stT162 50 := by
  have hc : ((220639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312030542107/2500000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((220639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c51 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-455933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3398253/5000000) (δ := 8227/1000000000) (ψ := -364563/1000000) 162 101
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t51 : ((-319234662099/2500000000000 : ℚ) : ℝ) ≤ stT162 51 := by
  have hc : ((-227979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319234662099/2500000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-227979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c52 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((913557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1047127/10000000) (δ := 4067/500000000) (ψ := -364563/1000000) 162 102
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t52 : ((5067223329/40000000000 : ℚ) : ℝ) ≤ stT162 52 := by
  have hc : ((913507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5067223329/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((913507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c53 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-44473/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3333697/5000000) (δ := 4067/500000000) (ψ := -364563/1000000) 162 102
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t53 : ((-61091813653/500000000000 : ℚ) : ℝ) ≤ stT162 53 := by
  have hc : ((-88951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61091813653/500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-88951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c54 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((103999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1470269/10000000) (δ := 4081/500000000) (ψ := -364563/1000000) 162 103
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t54 : ((566064568017/5000000000000 : ℚ) : ℝ) ≤ stT162 54 := by
  have hc : ((415971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((566064568017/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((415971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c55 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-726799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5961117/10000000) (δ := 8241/1000000000) (ψ := -364563/1000000) 162 103
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t55 : ((-2450207979/25000000000 : ℚ) : ℝ) ≤ stT162 55 := by
  have hc : ((-726849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2450207979/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-726849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c56 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((557237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1224677/5000000) (δ := 2037/250000000) (ψ := -364563/1000000) 162 104
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t56 : ((372286165611/5000000000000 : ℚ) : ℝ) ≤ stT162 56 := by
  have hc : ((557187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372286165611/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((557187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c57 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-12461/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589873/1250000) (δ := 2037/250000000) (ψ := -364563/1000000) 162 104
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t57 : ((-16507654779/400000000000 : ℚ) : ℝ) ≤ stT162 57 := by
  have hc : ((-12463/40000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16507654779/400000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-12463/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c58 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-1831/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39453/100000) (δ := 1651/200000000) (ψ := -364563/1000000) 162 105
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t58 : ((-968254131/1000000000000 : ℚ) : ℝ) ≤ stT162 58 := by
  have hc : ((-3687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-968254131/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-3687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c59 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((370571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 744483/2500000) (δ := 1651/200000000) (ψ := -364563/1000000) 162 105
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t59 : ((482377214169/10000000000000 : ℚ) : ℝ) ≤ stT162 59 := by
  have hc : ((370521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482377214169/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((370521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c60 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-716287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1480789/2500000) (δ := 8163/1000000000) (ψ := -364563/1000000) 162 106
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t60 : ((-184957497063/2000000000000 : ℚ) : ℝ) ≤ stT162 60 := by
  have hc : ((-716337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184957497063/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-716337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c61 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((190559/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77121/1000000) (δ := 103/12500000) (ψ := -364563/1000000) 162 106
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t61 : ((15248302627/125000000000 : ℚ) : ℝ) ≤ stT162 61 := by
  have hc : ((190549/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15248302627/125000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((190549/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c62 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-980283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7356713/10000000) (δ := 8163/1000000000) (ψ := -364563/1000000) 162 106
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t62 : ((-622512435333/5000000000000 : ℚ) : ℝ) ≤ stT162 62 := by
  have hc : ((-980333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-622512435333/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-980333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c63 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((146551/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116943/625000) (δ := 827/100000000) (ψ := -364563/1000000) 162 107
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t63 : ((184624221621/2000000000000 : ℚ) : ℝ) ≤ stT162 63 := by
  have hc : ((146541/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184624221621/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((146541/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c64 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-229917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4506973/10000000) (δ := 8133/1000000000) (ψ := -364563/1000000) 162 107
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t64 : ((-287458979967/10000000000000 : ℚ) : ℝ) ≤ stT162 64 := by
  have hc : ((-229967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287458979967/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-229967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c65 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-387501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4921789/10000000) (δ := 8177/1000000000) (ψ := -364563/1000000) 162 108
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t65 : ((-120174526937/2500000000000 : ℚ) : ℝ) ≤ stT162 65 := by
  have hc : ((-387551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120174526937/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-387551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c66 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((875359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 315387/2500000) (δ := 4113/500000000) (ψ := -364563/1000000) 162 108
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t66 : ((538715051213/5000000000000 : ℚ) : ℝ) ≤ stT162 66 := by
  have hc : ((875309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538715051213/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((875309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c67 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-979901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3675949/5000000) (δ := 8177/1000000000) (ψ := -364563/1000000) 162 108
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t67 : ((-239440247389/2000000000000 : ℚ) : ℝ) ≤ stT162 67 := by
  have hc : ((-979951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239440247389/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-979951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c68 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((73483/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47119/200000) (δ := 8119/1000000000) (ψ := -364563/1000000) 162 109
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t68 : ((178207276473/2500000000000 : ℚ) : ℝ) ≤ stT162 68 := by
  have hc : ((293907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178207276473/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((293907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c69 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((147629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 889141/2500000) (δ := 8119/1000000000) (ψ := -364563/1000000) 162 109
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t69 : ((88832079891/5000000000000 : ℚ) : ℝ) ≤ stT162 69 := by
  have hc : ((147579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88832079891/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((147579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c70 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-818499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -790497/1250000) (δ := 2053/250000000) (ψ := -364563/1000000) 162 110
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t70 : ((-978353502721/10000000000000 : ℚ) : ℝ) ≤ stT162 70 := by
  have hc : ((-818549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-978353502721/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-818549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c71 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((973281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579213/10000000) (δ := 2053/250000000) (ψ := -364563/1000000) 162 110
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t71 : ((1155012059411/10000000000000 : ℚ) : ℝ) ≤ stT162 71 := by
  have hc : ((973231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1155012059411/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((973231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c72 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-223451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5085239/10000000) (δ := 8191/1000000000) (ψ := -364563/1000000) 162 110
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t72 : ((-4115142933/78125000000 : ℚ) : ℝ) ≤ stT162 72 := by
  have hc : ((-55869/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4115142933/78125000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-55869/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c73 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-85871/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2518219/5000000) (δ := 1621/200000000) (ψ := -364563/1000000) 162 111
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t73 : ((-25129038243/500000000000 : ℚ) : ℝ) ≤ stT162 73 := by
  have hc : ((-85881/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25129038243/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-85881/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c74 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((982093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47383/1000000) (δ := 1621/200000000) (ψ := -364563/1000000) 162 111
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t74 : ((285400354617/2500000000000 : ℚ) : ℝ) ≤ stT162 74 := by
  have hc : ((982043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285400354617/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((982043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c75 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-712657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2955093/5000000) (δ := 4149/500000000) (ψ := -364563/1000000) 162 111
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t75 : ((-822963485607/10000000000000 : ℚ) : ℝ) ≤ stT162 75 := by
  have hc : ((-712707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-822963485607/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-712707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c76 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-201209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69273/156250) (δ := 8197/1000000000) (ψ := -364563/1000000) 162 112
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t76 : ((-230859972461/10000000000000 : ℚ) : ℝ) ≤ stT162 76 := by
  have hc : ((-201259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230859972461/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-201259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c77 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((188263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 860729/10000000) (δ := 4103/500000000) (ψ := -364563/1000000) 162 112
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t77 : ((42906812013/400000000000 : ℚ) : ℝ) ≤ stT162 77 := by
  have hc : ((188253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42906812013/400000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((188253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c78 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-380173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3043303/5000000) (δ := 4103/500000000) (ψ := -364563/1000000) 162 112
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t78 : ((-107622457761/1250000000000 : ℚ) : ℝ) ≤ stT162 78 := by
  have hc : ((-190099/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107622457761/1250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-190099/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c79 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-212399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4462063/10000000) (δ := 829/100000000) (ψ := -364563/1000000) 162 113
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t79 : ((-7469494391/312500000000 : ℚ) : ℝ) ≤ stT162 79 := by
  have hc : ((-212449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7469494391/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-212449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c80 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((968181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 632351/10000000) (δ := 829/100000000) (ψ := -364563/1000000) 162 113
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t80 : ((1082402406323/10000000000000 : ℚ) : ℝ) ≤ stT162 80 := by
  have hc : ((968131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1082402406323/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((968131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c81 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-64007/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 707933/1250000) (δ := 8113/1000000000) (ψ := -364563/1000000) 162 113
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t81 : ((-2222640667/31250000000 : ℚ) : ℝ) ≤ stT162 81 := by
  have hc : ((-16003/25000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2222640667/31250000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-16003/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c82 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-443273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5075109/10000000) (δ := 8183/1000000000) (ψ := -364563/1000000) 162 114
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t82 : ((-122392170517/2500000000000 : ℚ) : ℝ) ≤ stT162 82 := by
  have hc : ((-443323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122392170517/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-443323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c83 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((498899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82971/5000000) (δ := 8183/1000000000) (ψ := -364563/1000000) 162 114
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t83 : ((136896263777/1250000000000 : ℚ) : ℝ) ≤ stT162 83 := by
  have hc : ((249437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136896263777/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((249437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c84 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-5967/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4684399/10000000) (δ := 811/50000000) (ψ := -364563/1000000) 162 114
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t84 : ((-40697657/1250000000 : ℚ) : ℝ) ≤ stT162 84 := by
  have hc : ((-373/1250 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40697657/1250000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-373/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c85 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-398239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1557653/2500000) (δ := 8127/1000000000) (ψ := -364563/1000000) 162 115
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t85 : ((-53997280299/625000000000 : ℚ) : ℝ) ≤ stT162 85 := by
  have hc : ((-49783/62500 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53997280299/625000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-49783/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c86 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((826749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373433/2500000) (δ := 8127/1000000000) (ψ := -364563/1000000) 162 115
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t86 : ((891451852573/10000000000000 : ℚ) : ℝ) ≤ stT162 86 := by
  have hc : ((826699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((891451852573/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((826699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c87 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((58229/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199277/625000) (δ := 2069/250000000) (ψ := -364563/1000000) 162 115
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t87 : ((3901080533/125000000000 : ℚ) : ℝ) ≤ stT162 87 := by
  have hc : ((58219/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3901080533/125000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((58219/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c88 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-999891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 244283/312500) (δ := 8127/1000000000) (ψ := -364563/1000000) 162 115
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t88 : ((-266485276441/2500000000000 : ℚ) : ℝ) ≤ stT162 88 := by
  have hc : ((-999941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266485276441/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-999941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c89 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((24251/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -331461/1000000) (δ := 8169/1000000000) (ψ := -364563/1000000) 162 116
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t89 : ((12850343631/500000000000 : ℚ) : ℝ) ≤ stT162 89 := by
  have hc : ((12123/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12850343631/500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((12123/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c90 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((885033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1210577/10000000) (δ := 4117/500000000) (ψ := -364563/1000000) 162 116
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t90 : ((233213375109/2500000000000 : ℚ) : ℝ) ≤ stT162 90 := by
  have hc : ((884983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233213375109/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((884983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c91 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-323449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2842883/5000000) (δ := 8117/500000000) (ψ := -364563/1000000) 162 116
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t91 : ((-33909294209/500000000000 : ℚ) : ℝ) ≤ stT162 91 := by
  have hc : ((-161737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33909294209/500000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-161737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c92 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-123817/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1398983/2500000) (δ := 4071/500000000) (ψ := -364563/1000000) 162 117
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t92 : ((-129098686871/2000000000000 : ℚ) : ℝ) ≤ stT162 92 := by
  have hc : ((-123827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129098686871/2000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-123827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c93 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((883737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -608759/5000000) (δ := 8261/1000000000) (ψ := -364563/1000000) 162 117
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t93 : ((916340118337/10000000000000 : ℚ) : ℝ) ≤ stT162 93 := by
  have hc : ((883687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((916340118337/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((883687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c94 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((63893/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3114079/10000000) (δ := 4071/500000000) (ψ := -364563/1000000) 162 117
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t94 : ((65890267743/2000000000000 : ℚ) : ℝ) ≤ stT162 94 := by
  have hc : ((63883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65890267743/2000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((63883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c95 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-196709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7399829/10000000) (δ := 8261/1000000000) (ψ := -364563/1000000) 162 117
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t95 : ((-201829562901/2000000000000 : ℚ) : ℝ) ≤ stT162 95 := by
  have hc : ((-196719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201829562901/2000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-196719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c96 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-56077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4067257/10000000) (δ := 8249/1000000000) (ψ := -364563/1000000) 162 118
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t96 : ((-57284394867/10000000000000 : ℚ) : ℝ) ≤ stT162 96 := by
  have hc : ((-56127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57284394867/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-56127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c97 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((199731/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129677/10000000) (δ := 8249/1000000000) (ψ := -364563/1000000) 162 118
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t97 : ((101392959233/1000000000000 : ℚ) : ℝ) ≤ stT162 97 := by
  have hc : ((199721/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101392959233/1000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((199721/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c98 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-2221/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4283559/10000000) (δ := 4077/500000000) (ψ := -364563/1000000) 162 118
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t98 : ((-71818847841/5000000000000 : ℚ) : ℝ) ≤ stT162 98 := by
  have hc : ((-71097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71818847841/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-71097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c99 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-976651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3656341/5000000) (δ := 2039/250000000) (ψ := -364563/1000000) 162 119
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t99 : ((-490810809819/5000000000000 : ℚ) : ℝ) ≤ stT162 99 := by
  have hc : ((-976701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490810809819/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-976701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c100 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((270461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3242311/10000000) (δ := 8247/1000000000) (ψ := -364563/1000000) 162 119
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t100 : ((270410729589/10000000000000 : ℚ) : ℝ) ≤ stT162 100 := by
  have hc : ((270411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270410729589/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((270411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c101 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((14856/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 787601/10000000) (δ := 8247/1000000000) (ψ := -364563/1000000) 162 119
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t101 : ((473007753579/5000000000000 : ℚ) : ℝ) ≤ stT162 101 := by
  have hc : ((475367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((473007753579/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((475367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c102 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-166893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4777783/10000000) (δ := 2039/250000000) (ψ := -364563/1000000) 162 119
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t102 : ((-20659190483/625000000000 : ℚ) : ℝ) ≤ stT162 102 := by
  have hc : ((-83459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20659190483/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-83459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c103 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-93937/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87237/125000) (δ := 407/50000000) (ψ := -364563/1000000) 162 120
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t103 : ((-4628193543/50000000000 : ℚ) : ℝ) ≤ stT162 103 := by
  have hc : ((-46971/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4628193543/50000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-46971/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c104 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((33767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -306589/1000000) (δ := 8263/1000000000) (ψ := -364563/1000000) 162 120
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t104 : ((827658549/25000000000 : ℚ) : ℝ) ≤ stT162 104 := by
  have hc : ((16881/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((827658549/25000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((16881/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c105 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((948001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 809757/10000000) (δ := 407/50000000) (ψ := -364563/1000000) 162 120
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t105 : ((9251053809/100000000000 : ℚ) : ℝ) ≤ stT162 105 := by
  have hc : ((947951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9251053809/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((947951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c106 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-35583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4648631/10000000) (δ := 8263/1000000000) (ψ := -364563/1000000) 162 120
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t106 : ((-69134680551/2500000000000 : ℚ) : ℝ) ≤ stT162 106 := by
  have hc : ((-142357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69134680551/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-142357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c107 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-485787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -453529/625000) (δ := 8233/1000000000) (ψ := -364563/1000000) 162 121
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t107 : ((-117413108861/1250000000000 : ℚ) : ℝ) ≤ stT162 107 := by
  have hc : ((-121453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117413108861/1250000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-121453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c108 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((34861/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -109031/312500) (δ := 8233/1000000000) (ψ := -364563/1000000) 162 121
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t108 : ((134141499/8000000000 : ℚ) : ℝ) ≤ stT162 108 := by
  have hc : ((34851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134141499/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((34851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c109 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((995251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243731/10000000) (δ := 8233/1000000000) (ψ := -364563/1000000) 162 121
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t109 : ((476614696513/5000000000000 : ℚ) : ℝ) ≤ stT162 109 := by
  have hc : ((995201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476614696513/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((995201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c110 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-6161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1971197/5000000) (δ := 817/100000000) (ψ := -364563/1000000) 162 121
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t110 : ((-5921958693/10000000000000 : ℚ) : ℝ) ≤ stT162 110 := by
  have hc : ((-6211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5921958693/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-6211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c111 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-248787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7607603/10000000) (δ := 8233/1000000000) (ψ := -364563/1000000) 162 121
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t111 : ((-236150035821/2500000000000 : ℚ) : ℝ) ≤ stT162 111 := by
  have hc : ((-497599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236150035821/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-497599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c112 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-214749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4468077/10000000) (δ := 4063/500000000) (ψ := -364563/1000000) 162 122
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t112 : ((-12685384543/625000000000 : ℚ) : ℝ) ≤ stT162 112 := by
  have hc : ((-214799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12685384543/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-214799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c113 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((37613/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13563/156250) (δ := 4063/500000000) (ψ := -364563/1000000) 162 122
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t113 : ((442267749/5000000000 : ℚ) : ℝ) ≤ stT162 113 := by
  have hc : ((37611/40000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((442267749/5000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((37611/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c114 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((117809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2700261/10000000) (δ := 4063/500000000) (ψ := -364563/1000000) 162 122
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t114 : ((44130573981/1000000000000 : ℚ) : ℝ) ≤ stT162 114 := by
  have hc : ((235593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44130573981/1000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((235593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c115 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-19953/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 623741/1000000) (δ := 8277/1000000000) (ψ := -364563/1000000) 162 122
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t115 : ((-14885950317/200000000000 : ℚ) : ℝ) ≤ stT162 115 := by
  have hc : ((-79817/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14885950317/200000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-79817/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c116 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-90951/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186377/312500) (δ := 4109/500000000) (ψ := -364563/1000000) 162 123
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t116 : ((-337806858433/5000000000000 : ℚ) : ℝ) ≤ stT162 116 := by
  have hc : ((-363829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337806858433/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-363829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c117 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((544461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19901/80000) (δ := 4109/500000000) (ψ := -364563/1000000) 162 123
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t117 : ((1006615939/20000000000 : ℚ) : ℝ) ≤ stT162 117 := by
  have hc : ((544411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1006615939/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((544411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c118 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((231823/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 959209/10000000) (δ := 1637/200000000) (ψ := -364563/1000000) 162 123
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t118 : ((213398719227/2500000000000 : ℚ) : ℝ) ≤ stT162 118 := by
  have hc : ((463621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213398719227/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((463621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c119 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-179003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4376923/10000000) (δ := 1637/200000000) (ψ := -364563/1000000) 162 123
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t119 : ((-164137706047/10000000000000 : ℚ) : ℝ) ≤ stT162 119 := by
  have hc : ((-179053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164137706047/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-179053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c120 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-499691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1941521/2500000) (δ := 4109/500000000) (ψ := -364563/1000000) 162 123
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t120 : ((-114044061159/1250000000000 : ℚ) : ℝ) ≤ stT162 120 := by
  have hc : ((-124929/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114044061159/1250000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-124929/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c121 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-129289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -916173/2000000) (δ := 8111/1000000000) (ψ := -364563/1000000) 162 124
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t121 : ((-58779096787/2500000000000 : ℚ) : ℝ) ≤ stT162 121 := by
  have hc : ((-64657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58779096787/2500000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-64657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c122 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((878059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155939/1250000) (δ := 2073/250000000) (ψ := -364563/1000000) 162 124
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t122 : ((794911594213/10000000000000 : ℚ) : ℝ) ≤ stT162 122 := by
  have hc : ((878009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((794911594213/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((878009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c123 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((135939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16083/78125) (δ := 8111/1000000000) (ψ := -364563/1000000) 162 124
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t123 : ((122562965501/2000000000000 : ℚ) : ℝ) ≤ stT162 123 := by
  have hc : ((135929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122562965501/2000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((135929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c124 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-534909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 533799/1000000) (δ := 8111/1000000000) (ψ := -364563/1000000) 162 124
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t124 : ((-480407625893/10000000000000 : ℚ) : ℝ) ≤ stT162 124 := by
  have hc : ((-534959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-480407625893/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-534959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c125 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-191371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1779233/2500000) (δ := 8199/1000000000) (ψ := -364563/1000000) 162 125
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t125 : ((-42794131267/500000000000 : ℚ) : ℝ) ≤ stT162 125 := by
  have hc : ((-191381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42794131267/500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-191381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c126 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((14871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3889811/10000000) (δ := 8199/1000000000) (ψ := -364563/1000000) 162 125
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t126 : ((1320358427/1000000000000 : ℚ) : ℝ) ≤ stT162 126 := by
  have hc : ((14821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1320358427/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((14821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c127 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((120293/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -344123/5000000) (δ := 2051/250000000) (ψ := -364563/1000000) 162 125
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t127 : ((106737169333/1250000000000 : ℚ) : ℝ) ≤ stT162 127 := by
  have hc : ((481147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106737169333/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((481147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c128 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((544251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9953/40000) (δ := 2051/250000000) (ψ := -364563/1000000) 162 125
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t128 : ((481010012483/10000000000000 : ℚ) : ℝ) ≤ stT162 128 := by
  have hc : ((544201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((481010012483/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((544201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c129 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-632843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5640041/10000000) (δ := 2051/250000000) (ψ := -364563/1000000) 162 125
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t129 : ((-557231274743/10000000000000 : ℚ) : ℝ) ≤ stT162 129 := by
  have hc : ((-632893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557231274743/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-632893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c130 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-186797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216891/312500) (δ := 4053/500000000) (ψ := -364563/1000000) 162 126
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t130 : ((-163840760613/2000000000000 : ℚ) : ℝ) ≤ stT162 130 := by
  have hc : ((-186807/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163840760613/2000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-186807/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c131 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((35973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1918519/5000000) (δ := 8297/1000000000) (ψ := -364563/1000000) 162 126
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t131 : ((3923258599/1250000000000 : ℚ) : ℝ) ≤ stT162 131 := by
  have hc : ((35923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3923258599/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((35923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c132 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((238621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30287/400000) (δ := 8297/1000000000) (ψ := -364563/1000000) 162 126
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t132 : ((103840987549/1250000000000 : ℚ) : ℝ) ≤ stT162 132 := by
  have hc : ((477217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103840987549/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((477217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c133 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((302999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2299441/10000000) (δ := 8297/1000000000) (ψ := -364563/1000000) 162 126
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t133 : ((131355741083/2500000000000 : ℚ) : ℝ) ≤ stT162 133 := by
  have hc : ((151487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131355741083/2500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((151487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c134 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-266637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1066631/2000000) (δ := 8153/500000000) (ψ := -364563/1000000) 162 126
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t134 : ((-115180517639/2500000000000 : ℚ) : ℝ) ≤ stT162 134 := by
  have hc : ((-133331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115180517639/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-133331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c135 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-245207/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3681827/5000000) (δ := 819/100000000) (ψ := -364563/1000000) 162 127
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t135 : ((-422102701057/5000000000000 : ℚ) : ℝ) ≤ stT162 135 := by
  have hc : ((-490439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422102701057/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-490439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c136 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-178133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4374713/10000000) (δ := 8213/1000000000) (ψ := -364563/1000000) 162 127
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t136 : ((-152790675219/10000000000000 : ℚ) : ℝ) ≤ stT162 136 := by
  have hc : ((-178183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152790675219/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-178183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c137 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((845627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1407643/10000000) (δ := 819/100000000) (ψ := -364563/1000000) 162 127
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t137 : ((722424628989/10000000000000 : ℚ) : ℝ) ≤ stT162 137 := by
  have hc : ((845577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((722424628989/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((845577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c138 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((12761/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1537801/10000000) (δ := 8213/1000000000) (ψ := -364563/1000000) 162 127
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t138 : ((43448851089/625000000000 : ℚ) : ℝ) ≤ stT162 138 := by
  have hc : ((408327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43448851089/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((408327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c139 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-212383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2231011/5000000) (δ := 819/100000000) (ψ := -364563/1000000) 162 127
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t139 : ((-180183333837/10000000000000 : ℚ) : ℝ) ≤ stT162 139 := by
  have hc : ((-212433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180183333837/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-212433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c140 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-980953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473053/2000000) (δ := 8213/1000000000) (ψ := -364563/1000000) 162 127
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t140 : ((-165819918093/2000000000000 : ℚ) : ℝ) ≤ stT162 140 := by
  have hc : ((-981003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165819918093/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-981003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c141 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-28777/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -682519/1250000) (δ := 8283/1000000000) (ψ := -364563/1000000) 162 128
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t141 : ((-6059178371/125000000000 : ℚ) : ℝ) ≤ stT162 141 := by
  have hc : ((-57559/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6059178371/125000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-57559/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c142 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((126733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162371/625000) (δ := 8283/1000000000) (ψ := -364563/1000000) 162 128
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t142 : ((212682871821/5000000000000 : ℚ) : ℝ) ≤ stT162 142 := by
  have hc : ((253441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212682871821/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((253441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c143 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((995233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7631/312500) (δ := 8283/1000000000) (ψ := -364563/1000000) 162 128
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t143 : ((416106911143/5000000000000 : ℚ) : ℝ) ≤ stT162 143 := by
  have hc : ((995183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416106911143/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((995183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c144 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((6749/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122659/400000) (δ := 8283/1000000000) (ψ := -364563/1000000) 162 128
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t144 : ((1405832771/50000000000 : ℚ) : ℝ) ≤ stT162 144 := by
  have hc : ((1687/5000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1405832771/50000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((1687/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c145 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-701083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2934639/5000000) (δ := 203/25000000) (ψ := -364563/1000000) 162 128
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t145 : ((-116451881103/2000000000000 : ℚ) : ℝ) ≤ stT162 145 := by
  have hc : ((-701133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116451881103/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-701133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c146 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-118673/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7055161/10000000) (δ := 327/40000000) (ψ := -364563/1000000) 162 129
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t146 : ((-196439318751/2500000000000 : ℚ) : ℝ) ≤ stT162 146 := by
  have hc : ((-474717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196439318751/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-474717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c147 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-453/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4290671/10000000) (δ := 2057/250000000) (ψ := -364563/1000000) 162 129
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t147 : ((-11960236287/1000000000000 : ℚ) : ℝ) ≤ stT162 147 := by
  have hc : ((-14501/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11960236287/1000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-14501/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c148 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((101883/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544893/10000000) (δ := 327/40000000) (ψ := -364563/1000000) 162 129
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t148 : ((167484154479/2500000000000 : ℚ) : ℝ) ≤ stT162 148 := by
  have hc : ((407507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167484154479/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((407507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c149 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((890221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591209/5000000) (δ := 2057/250000000) (ψ := -364563/1000000) 162 129
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t149 : ((729255678501/10000000000000 : ℚ) : ℝ) ≤ stT162 149 := by
  have hc : ((890171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((729255678501/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((890171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c150 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((14227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1945711/5000000) (δ := 327/40000000) (ψ := -364563/1000000) 162 129
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t150 : ((723466487/625000000000 : ℚ) : ℝ) ≤ stT162 150 := by
  have hc : ((14177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((723466487/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((14177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c151 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-218357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316497/2000000) (δ := 327/40000000) (ψ := -364563/1000000) 162 129
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t151 : ((-355413394071/5000000000000 : ℚ) : ℝ) ≤ stT162 151 := by
  have hc : ((-436739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355413394071/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-436739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c152 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-271/320 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1290439/2000000) (δ := 2067/250000000) (ψ := -364563/1000000) 162 130
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t152 : ((-6869476429/100000000000 : ℚ) : ℝ) ≤ stT162 152 := by
  have hc : ((-33877/40000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6869476429/100000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-33877/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c153 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((52193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118639/312500) (δ := 2067/250000000) (ψ := -364563/1000000) 162 130
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t153 : ((10538778159/2500000000000 : ℚ) : ℝ) ≤ stT162 153 := by
  have hc : ((52143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10538778159/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((52143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c154 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((223657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -578997/5000000) (δ := 1627/200000000) (ψ := -364563/1000000) 162 130
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t154 : ((180217658279/2500000000000 : ℚ) : ℝ) ≤ stT162 154 := by
  have hc : ((447289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180217658279/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((447289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c155 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((10419/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182921/1250000) (δ := 2067/250000000) (ψ := -364563/1000000) 162 130
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t155 : ((66945893993/1000000000000 : ℚ) : ℝ) ≤ stT162 155 := by
  have hc : ((83347/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66945893993/1000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((83347/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c156 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-56327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4067883/10000000) (δ := 1627/200000000) (ψ := -364563/1000000) 162 130
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t156 : ((-45137737657/10000000000000 : ℚ) : ℝ) ≤ stT162 156 := by
  have hc : ((-56377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45137737657/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-56377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c157 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-443661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 831969/1250000) (δ := 1627/200000000) (ψ := -364563/1000000) 162 130
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t157 : ((-177050014341/2500000000000 : ℚ) : ℝ) ≤ stT162 157 := by
  have hc : ((-221843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177050014341/2500000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-221843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c158 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-852901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1296157/2000000) (δ := 4121/500000000) (ψ := -364563/1000000) 162 131
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t158 : ((-339285995829/5000000000000 : ℚ) : ℝ) ≤ stT162 158 := by
  have hc : ((-852951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339285995829/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-852951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c159 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3925559/10000000) (δ := 4121/500000000) (ψ := -364563/1000000) 162 131
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t159 : ((414765673/10000000000000 : ℚ) : ℝ) ≤ stT162 159 := by
  have hc : ((523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414765673/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c160 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((425069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1386371/10000000) (δ := 4121/500000000) (ψ := -364563/1000000) 162 131
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t160 : ((84006652509/1250000000000 : ℚ) : ℝ) ≤ stT162 160 := by
  have hc : ((106261/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84006652509/1250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((106261/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c161 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((56147/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1136981/10000000) (δ := 8161/1000000000) (ψ := -364563/1000000) 162 131
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t161 : ((35398039461/500000000000 : ℚ) : ℝ) ≤ stT162 161 := by
  have hc : ((449151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35398039461/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((449151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c162 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((5633/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3644741/10000000) (δ := 8161/1000000000) (ψ := -364563/1000000) 162 131
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t162 : ((4423737457/500000000000 : ℚ) : ℝ) ≤ stT162 162 := by
  have hc : ((11261/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4423737457/500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((11261/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c163 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-386651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6137071/10000000) (δ := 4121/500000000) (ψ := -364563/1000000) 162 131
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t163 : ((-75717057609/1250000000000 : ℚ) : ℝ) ≤ stT162 163 := by
  have hc : ((-96669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75717057609/1250000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-96669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c164 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-954129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -886729/1250000) (δ := 4127/500000000) (ψ := -364563/1000000) 162 132
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t164 : ((-745088801551/10000000000000 : ℚ) : ℝ) ≤ stT162 164 := by
  have hc : ((-954179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-745088801551/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-954179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c165 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-139109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4631837/10000000) (δ := 4127/500000000) (ψ := -364563/1000000) 162 132
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t165 : ((-54157839933/2500000000000 : ℚ) : ℝ) ≤ stT162 165 := by
  have hc : ((-69567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54157839933/2500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-69567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c166 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((128371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -436941/2000000) (δ := 8149/1000000000) (ψ := -364563/1000000) 162 132
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t166 : ((1992547803/40000000000 : ℚ) : ℝ) ≤ stT162 166 := by
  have hc : ((128361/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1992547803/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((128361/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c167 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((995093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49553/2000000) (δ := 4127/500000000) (ψ := -364563/1000000) 162 132
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t167 : ((769987159389/10000000000000 : ℚ) : ℝ) ≤ stT162 167 := by
  have hc : ((995043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((769987159389/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((995043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c168 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((483399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 333207/1250000) (δ := 8149/1000000000) (ψ := -364563/1000000) 162 132
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t168 : ((93227871771/2500000000000 : ℚ) : ℝ) ≤ stT162 168 := by
  have hc : ((483349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93227871771/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((483349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c169 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-110293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20277/40000) (δ := 8149/1000000000) (ψ := -364563/1000000) 162 132
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t169 : ((-169700820141/5000000000000 : ℚ) : ℝ) ≤ stT162 169 := by
  have hc : ((-220611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169700820141/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-220611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c170 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-493761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1864657/2500000) (δ := 4127/500000000) (ψ := -364563/1000000) 162 132
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t170 : ((-37871657949/500000000000 : ℚ) : ℝ) ≤ stT162 170 := by
  have hc : ((-246893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37871657949/500000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-246893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c171 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-35121/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5873969/10000000) (δ := 129/15625000) (ψ := -364563/1000000) 162 133
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t171 : ((-671491073/12500000000 : ℚ) : ℝ) ≤ stT162 171 := by
  have hc : ((-70247/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-671491073/12500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-70247/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c172 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((2579/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -702491/2000000) (δ := 8147/1000000000) (ψ := -364563/1000000) 162 133
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t172 : ((15726969369/1250000000000 : ℚ) : ℝ) ≤ stT162 172 := by
  have hc : ((82503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15726969369/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((82503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c173 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((893439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1164629/10000000) (δ := 129/15625000) (ψ := -364563/1000000) 162 133
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t173 : ((135846051173/2000000000000 : ℚ) : ℝ) ≤ stT162 173 := by
  have hc : ((893389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135846051173/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((893389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c174 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((223133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1169669/10000000) (δ := 8147/1000000000) (ψ := -364563/1000000) 162 133
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t174 : ((169147204809/2500000000000 : ℚ) : ℝ) ≤ stT162 174 := by
  have hc : ((446241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169147204809/2500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((446241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c175 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((17367/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3490603/10000000) (δ := 129/15625000) (ψ := -364563/1000000) 162 133
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t175 : ((820276371/62500000000 : ℚ) : ℝ) ≤ stT162 175 := by
  have hc : ((8681/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((820276371/62500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((8681/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c176 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-170139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5798293/10000000) (δ := 129/15625000) (ψ := -364563/1000000) 162 133
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t176 : ((-256513255037/5000000000000 : ℚ) : ℝ) ≤ stT162 176 := by
  have hc : ((-340303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256513255037/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-340303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c177 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-199087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3807511/5000000) (δ := 8239/1000000000) (ψ := -364563/1000000) 162 134
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t177 : ((-149650662759/2000000000000 : ℚ) : ℝ) ≤ stT162 177 := by
  have hc : ((-199097/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149650662759/2000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-199097/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c178 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-266667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5333333/10000000) (δ := 8239/1000000000) (ψ := -364563/1000000) 162 134
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t178 : ((-12493386759/312500000000 : ℚ) : ℝ) ≤ stT162 178 := by
  have hc : ((-66673/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12493386759/312500000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-66673/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c179 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((33823/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3064401/10000000) (δ := 2041/250000000) (ψ := -364563/1000000) 162 134
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t179 : ((2527675683/100000000000 : ℚ) : ℝ) ≤ stT162 179 := by
  have hc : ((16909/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2527675683/100000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((16909/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c180 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((189641/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404073/5000000) (δ := 2041/250000000) (ψ := -364563/1000000) 162 134
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t180 : ((28268482801/400000000000 : ℚ) : ℝ) ≤ stT162 180 := by
  have hc : ((189631/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28268482801/400000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((189631/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c181 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((419799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287127/2000000) (δ := 2041/250000000) (ψ := -364563/1000000) 162 134
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t181 : ((78003873889/1250000000000 : ℚ) : ℝ) ≤ stT162 181 := by
  have hc : ((209887/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78003873889/1250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((209887/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c182 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((519/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3667023/10000000) (δ := 2041/250000000) (ψ := -364563/1000000) 162 134
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t182 : ((61523667/8000000000 : ℚ) : ℝ) ≤ stT162 182 := by
  have hc : ((83/800 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61523667/8000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((83/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c183 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-705899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294311/500000) (δ := 8239/1000000000) (ψ := -364563/1000000) 162 134
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t183 : ((-260926515839/5000000000000 : ℚ) : ℝ) ≤ stT162 183 := by
  have hc : ((-705949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260926515839/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-705949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c184 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-995421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1522931/2000000) (δ := 2033/250000000) (ψ := -364563/1000000) 162 135
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t184 : ((-73387117591/1000000000000 : ℚ) : ℝ) ≤ stT162 184 := by
  have hc : ((-995471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73387117591/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-995471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c185 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-140543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2709757/5000000) (δ := 8271/1000000000) (ψ := -364563/1000000) 162 135
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t185 : ((-41335404773/1000000000000 : ℚ) : ℝ) ≤ stT162 185 := by
  have hc : ((-281111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41335404773/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-281111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c186 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((136399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40453/125000) (δ := 8271/1000000000) (ψ := -364563/1000000) 162 135
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t186 : ((9999418989/500000000000 : ℚ) : ℝ) ≤ stT162 186 := by
  have hc : ((68187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9999418989/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((68187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c187 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((910687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106463/1000000) (δ := 8271/1000000000) (ψ := -364563/1000000) 162 135
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t187 : ((83240417533/1250000000000 : ℚ) : ℝ) ≤ stT162 187 := by
  have hc : ((910637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83240417533/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((910637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c188 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((905541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273839/2500000) (δ := 2033/250000000) (ψ := -364563/1000000) 162 135
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t188 : ((165099079521/2500000000000 : ℚ) : ℝ) ≤ stT162 188 := by
  have hc : ((905491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165099079521/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((905491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c189 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((269841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1621961/5000000) (δ := 8271/1000000000) (ψ := -364563/1000000) 162 135
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t189 : ((6132619221/312500000000 : ℚ) : ℝ) ≤ stT162 189 := by
  have hc : ((269791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6132619221/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((269791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c190 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-2747/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5381107/10000000) (δ := 8271/1000000000) (ψ := -364563/1000000) 162 135
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t190 : ((-7972266753/200000000000 : ℚ) : ℝ) ≤ stT162 190 := by
  have hc : ((-10989/20000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7972266753/200000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-10989/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c191 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-99039/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3753557/5000000) (δ := 8271/1000000000) (ψ := -364563/1000000) 162 135
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t191 : ((-716657623/10000000000 : ℚ) : ℝ) ≤ stT162 191 := by
  have hc : ((-24761/25000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-716657623/10000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-24761/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c192 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-95023/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -304299/500000) (δ := 4089/500000000) (ψ := -364563/1000000) 162 136
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t192 : ((-34290734687/625000000000 : ℚ) : ℝ) ≤ stT162 192 := by
  have hc : ((-380117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34290734687/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-380117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c193 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-5509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1991043/5000000) (δ := 4089/500000000) (ψ := -364563/1000000) 162 136
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t193 : ((-993616011/625000000000 : ℚ) : ℝ) ≤ stT162 193 := by
  have hc : ((-11043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-993616011/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-11043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c194 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((90981/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -944523/5000000) (δ := 4089/500000000) (ψ := -364563/1000000) 162 136
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t194 : ((130632099121/2500000000000 : ℚ) : ℝ) ≤ stT162 194 := by
  have hc : ((363899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130632099121/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((363899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c195 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((199403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193221/10000000) (δ := 4089/500000000) (ψ := -364563/1000000) 162 136
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t195 : ((71394059401/1000000000000 : ℚ) : ℝ) ≤ stT162 195 := by
  have hc : ((199393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71394059401/1000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((199393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c196 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((12339/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 566209/2500000) (δ := 329/40000000) (ψ := -364563/1000000) 162 136
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t196 : ((881284833/20000000000 : ℚ) : ℝ) ≤ stT162 196 := by
  have hc : ((6169/10000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((881284833/20000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((6169/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c197 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-9931/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2162961/5000000) (δ := 4089/500000000) (ψ := -364563/1000000) 162 136
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t197 : ((-56622207783/5000000000000 : ℚ) : ℝ) ≤ stT162 197 := by
  have hc : ((-79473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56622207783/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-79473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c198 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-830401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3188279/5000000) (δ := 329/40000000) (ψ := -364563/1000000) 162 136
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t198 : ((-59017661217/1000000000000 : ℚ) : ℝ) ≤ stT162 198 := by
  have hc : ((-830451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59017661217/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-830451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c199 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-24369/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -911387/1250000) (δ := 4059/500000000) (ψ := -364563/1000000) 162 137
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t199 : ((-34551263121/500000000000 : ℚ) : ℝ) ≤ stT162 199 := by
  have hc : ((-97481/100000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34551263121/500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-97481/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c200 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-508651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5261033/10000000) (δ := 1657/200000000) (ψ := -364563/1000000) 162 137
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t200 : ((-359706038007/10000000000000 : ℚ) : ℝ) ≤ stT162 200 := by
  have hc : ((-508701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-359706038007/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-508701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c201 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((54189/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -648211/2000000) (δ := 1657/200000000) (ψ := -364563/1000000) 162 137
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t201 : ((7642977351/400000000000 : ℚ) : ℝ) ≤ stT162 201 := by
  have hc : ((54179/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7642977351/400000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((54179/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c202 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((88117/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -615581/5000000) (δ := 4059/500000000) (ψ := -364563/1000000) 162 137
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t202 : ((3874708679/62500000000 : ℚ) : ℝ) ≤ stT162 202 := by
  have hc : ((5507/6250 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3874708679/62500000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((5507/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c203 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((953081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15377/200000) (δ := 1657/200000000) (ψ := -364563/1000000) 162 137
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t203 : ((334448121861/5000000000000 : ℚ) : ℝ) ≤ stT162 203 := by
  have hc : ((953031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334448121861/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((953031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c204 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((225189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137951/500000) (δ := 1657/200000000) (ψ := -364563/1000000) 162 137
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t204 : ((1970579037/62500000000 : ℚ) : ℝ) ≤ stT162 204 := by
  have hc : ((56291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1970579037/62500000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((56291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c205 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-319301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 473947/1000000) (δ := 1657/200000000) (ψ := -364563/1000000) 162 137
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t205 : ((-223044638281/10000000000000 : ℚ) : ℝ) ≤ stT162 205 := by
  have hc : ((-319351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223044638281/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-319351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c206 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-56073/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6710281/10000000) (δ := 1657/200000000) (ψ := -364563/1000000) 162 137
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t206 : ((-156280571503/2500000000000 : ℚ) : ℝ) ≤ stT162 206 := by
  have hc : ((-448609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156280571503/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-448609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c207 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-236751/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703643/1000000) (δ := 8211/1000000000) (ψ := -364563/1000000) 162 138
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t207 : ((-329124467823/5000000000000 : ℚ) : ℝ) ≤ stT162 207 := by
  have hc : ((-473527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-329124467823/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-473527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c208 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-223339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5084613/10000000) (δ := 16/1953125) (ψ := -364563/1000000) 162 138
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t208 : ((-302490697/9765625000 : ℚ) : ℝ) ≤ stT162 208 := by
  have hc : ((-55841/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302490697/9765625000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-55841/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c209 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((77201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -392769/1250000) (δ := 16/1953125) (ψ := -364563/1000000) 162 138
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t209 : ((53392366089/2500000000000 : ℚ) : ℝ) ≤ stT162 209 := by
  have hc : ((154377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53392366089/2500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((154377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c210 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((885333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604483/5000000) (δ := 8211/1000000000) (ψ := -364563/1000000) 162 138
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t210 : ((122180562679/2000000000000 : ℚ) : ℝ) ≤ stT162 210 := by
  have hc : ((885283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122180562679/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((885283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c211 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((959377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715027/10000000) (δ := 8211/1000000000) (ψ := -364563/1000000) 162 138
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t211 : ((165106891989/2500000000000 : ℚ) : ℝ) ≤ stT162 211 := by
  have hc : ((959327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165106891989/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((959327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c212 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((495867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 657477/2500000) (δ := 16/1953125) (ψ := -364563/1000000) 162 138
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t212 : ((170264053617/5000000000000 : ℚ) : ℝ) ≤ stT162 212 := by
  have hc : ((495817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170264053617/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((495817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c213 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-241123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4535797/10000000) (δ := 8211/1000000000) (ψ := -364563/1000000) 162 138
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t213 : ((-165249086697/10000000000000 : ℚ) : ℝ) ≤ stT162 213 := by
  have hc : ((-241173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165249086697/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-241173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c214 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-842719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6432777/10000000) (δ := 16/1953125) (ψ := -364563/1000000) 162 138
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t214 : ((-288052544817/5000000000000 : ℚ) : ℝ) ≤ stT162 214 := by
  have hc : ((-842769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288052544817/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-842769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c215 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-982611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1846769/2500000) (δ := 8299/1000000000) (ψ := -364563/1000000) 162 139
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t215 : ((-134033977739/2000000000000 : ℚ) : ℝ) ≤ stT162 215 := by
  have hc : ((-982661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134033977739/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-982661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c216 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-590993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2753857/5000000) (δ := 8299/1000000000) (ψ := -364563/1000000) 162 139
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t216 : ((-201076965901/5000000000000 : ℚ) : ℝ) ≤ stT162 216 := by
  have hc : ((-591043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201076965901/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-591043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c217 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((115713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181853/500000) (δ := 1013/125000000) (ψ := -364563/1000000) 162 139
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t217 : ((19629283393/2500000000000 : ℚ) : ℝ) ≤ stT162 217 := by
  have hc : ((115663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19629283393/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((115663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c218 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((189591/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1774991/10000000) (δ := 8299/1000000000) (ψ := -364563/1000000) 162 139
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t218 : ((51359469749/1000000000000 : ℚ) : ℝ) ≤ stT162 218 := by
  have hc : ((379157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51359469749/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((379157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c219 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((499753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19643/2500000) (δ := 1013/125000000) (ψ := -364563/1000000) 162 139
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t219 : ((21105293721/312500000000 : ℚ) : ℝ) ≤ stT162 219 := by
  have hc : ((31233/31250 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21105293721/312500000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((31233/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c220 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((718281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1923671/10000000) (δ := 1013/125000000) (ψ := -364563/1000000) 162 139
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t220 : ((484230621969/10000000000000 : ℚ) : ℝ) ≤ stT162 220 := by
  have hc : ((718231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484230621969/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((718231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c221 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((4161/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3760427/10000000) (δ := 1013/125000000) (ψ := -364563/1000000) 162 139
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t221 : ((699221523/156250000000 : ℚ) : ℝ) ≤ stT162 221 := by
  have hc : ((33263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699221523/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((33263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c222 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-308427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139721/250000) (δ := 1013/125000000) (ψ := -364563/1000000) 162 139
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t222 : ((-51754929741/1250000000000 : ℚ) : ℝ) ≤ stT162 222 := by
  have hc : ((-77113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51754929741/1250000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-77113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c223 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-492103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 463067/625000) (δ := 1013/125000000) (ψ := -364563/1000000) 162 139
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t223 : ((-205970947/3125000000 : ℚ) : ℝ) ≤ stT162 223 := by
  have hc : ((-15379/15625 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205970947/3125000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-15379/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c224 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-170831/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16217/25000) (δ := 2049/250000000) (ψ := -364563/1000000) 162 140
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t224 : ((-57074048757/1000000000000 : ℚ) : ℝ) ≤ stT162 224 := by
  have hc : ((-170841/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57074048757/1000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-170841/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c225 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-297727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292673/625000) (δ := 2049/250000000) (ψ := -364563/1000000) 162 140
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t225 : ((-198518099259/10000000000000 : ℚ) : ℝ) ≤ stT162 225 := by
  have hc : ((-297777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198518099259/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-297777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c226 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((50523/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115471/400000) (δ := 16207/1000000000) (ψ := -364563/1000000) 162 140
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t226 : ((13441294773/500000000000 : ℚ) : ℝ) ≤ stT162 226 := by
  have hc : ((202067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13441294773/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((202067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c227 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((56561/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27467/250000) (δ := 2049/250000000) (ψ := -364563/1000000) 162 140
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t227 : ((300310099749/5000000000000 : ℚ) : ℝ) ≤ stT162 227 := by
  have hc : ((452463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300310099749/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((452463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c228 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((96307/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340769/5000000) (δ := 2049/250000000) (ψ := -364563/1000000) 162 140
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t228 : ((15944385083/250000000000 : ℚ) : ℝ) ≤ stT162 228 := by
  have hc : ((48151/50000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15944385083/250000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((48151/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c229 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((5557/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122699/500000) (δ := 2049/250000000) (ψ := -364563/1000000) 162 140
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t229 : ((3671835217/100000000000 : ℚ) : ℝ) ≤ stT162 229 := by
  have hc : ((11113/20000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3671835217/100000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((11113/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c230 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-58207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4218687/10000000) (δ := 8207/1000000000) (ψ := -364563/1000000) 162 140
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t230 : ((-4799634299/625000000000 : ℚ) : ℝ) ≤ stT162 230 := by
  have hc : ((-7279/62500 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4799634299/625000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-7279/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c231 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-182701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5975739/10000000) (δ := 8207/1000000000) (ψ := -364563/1000000) 162 140
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t231 : ((-7513544547/156250000000 : ℚ) : ℝ) ≤ stT162 231 := by
  have hc : ((-365427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7513544547/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-365427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c232 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-998673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7725177/10000000) (δ := 8207/1000000000) (ψ := -364563/1000000) 162 140
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t232 : ((-655694607359/10000000000000 : ℚ) : ℝ) ≤ stT162 232 := by
  have hc : ((-998723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-655694607359/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-998723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c233 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-399473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6240841/10000000) (δ := 4057/500000000) (ψ := -364563/1000000) 162 141
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t233 : ((-65429982189/1250000000000 : ℚ) : ℝ) ≤ stT162 233 := by
  have hc : ((-199749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65429982189/1250000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-199749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c234 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-114837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1126587/2500000) (δ := 8289/1000000000) (ψ := -364563/1000000) 162 141
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t234 : ((-37543850751/2500000000000 : ℚ) : ℝ) ≤ stT162 234 := by
  have hc : ((-57431/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37543850751/2500000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-57431/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c235 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((110783/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1389633/5000000) (δ := 8289/1000000000) (ψ := -364563/1000000) 162 141
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t235 : ((18064674681/625000000000 : ℚ) : ℝ) ≤ stT162 235 := by
  have hc : ((221541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18064674681/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((221541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c236 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((911531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529757/5000000) (δ := 4057/500000000) (ψ := -364563/1000000) 162 141
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t236 : ((9270673251/156250000000 : ℚ) : ℝ) ≤ stT162 236 := by
  have hc : ((911481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9270673251/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((911481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c237 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((483043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652947/10000000) (δ := 8289/1000000000) (ψ := -364563/1000000) 162 141
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t237 : ((156876759621/2500000000000 : ℚ) : ℝ) ≤ stT162 237 := by
  have hc : ((241509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156876759621/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((241509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c238 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((9174/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11791/50000) (δ := 4057/500000000) (ψ := -364563/1000000) 162 141
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t238 : ((190275453229/5000000000000 : ℚ) : ℝ) ≤ stT162 238 := by
  have hc : ((293543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190275453229/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((293543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c239 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-5171/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1014081/2500000) (δ := 8289/1000000000) (ψ := -364563/1000000) 162 141
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t239 : ((-418510009/125000000000 : ℚ) : ℝ) ≤ stT162 239 := by
  have hc : ((-647/12500 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418510009/125000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-647/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c240 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-41593/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5747361/10000000) (δ := 8289/1000000000) (ψ := -364563/1000000) 162 141
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t240 : ((-107400861981/2500000000000 : ℚ) : ℝ) ≤ stT162 240 := by
  have hc : ((-332769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107400861981/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-332769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c241 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-197149/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7431351/10000000) (δ := 8289/1000000000) (ψ := -364563/1000000) 162 141
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t241 : ((-127001349963/2000000000000 : ℚ) : ℝ) ≤ stT162 241 := by
  have hc : ((-197159/200000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127001349963/2000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-197159/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c242 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-876739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1649897/2500000) (δ := 4091/500000000) (ψ := -364563/1000000) 162 142
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t242 : ((-22544875557/400000000000 : ℚ) : ℝ) ≤ stT162 242 := by
  have hc : ((-876789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22544875557/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-876789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c243 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-390339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4929489/10000000) (δ := 8221/1000000000) (ψ := -364563/1000000) 162 142
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t243 : ((-250434933889/10000000000000 : ℚ) : ℝ) ≤ stT162 243 := by
  have hc : ((-390389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250434933889/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-390389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c244 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((65309/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -653247/2000000) (δ := 8221/1000000000) (ψ := -364563/1000000) 162 142
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t244 : ((10450443639/625000000000 : ℚ) : ℝ) ≤ stT162 244 := by
  have hc : ((130593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10450443639/625000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((130593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c245 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((799747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -804903/5000000) (δ := 8191/500000000) (ψ := -364563/1000000) 162 142
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t245 : ((127726805143/2500000000000 : ℚ) : ℝ) ≤ stT162 245 := by
  have hc : ((799697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127726805143/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((799697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c246 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((999873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39901/10000000) (δ := 4091/500000000) (ψ := -364563/1000000) 162 142
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t246 : ((79682893631/1250000000000 : ℚ) : ℝ) ≤ stT162 246 := by
  have hc : ((999823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79682893631/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((999823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c247 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((390927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 336581/2000000) (δ := 4091/500000000) (ψ := -364563/1000000) 162 142
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t247 : ((31090586021/625000000000 : ℚ) : ℝ) ≤ stT162 247 := by
  have hc : ((195451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31090586021/625000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((195451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c248 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((120351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3319267/10000000) (δ := 4091/500000000) (ψ := -364563/1000000) 162 142
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t248 : ((7640701/500000000 : ℚ) : ℝ) ≤ stT162 248 := by
  have hc : ((60163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7640701/500000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((60163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c249 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-198761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1237257/2500000) (δ := 8221/1000000000) (ψ := -364563/1000000) 162 142
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t249 : ((-2519513157/100000000000 : ℚ) : ℝ) ≤ stT162 249 := by
  have hc : ((-99393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2519513157/100000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-99393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_c250 :
    |Real.cos (((162 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((-435719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1643077/2500000) (δ := 4091/500000000) (ψ := -364563/1000000) 162 142
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st162_t250 : ((-1076519169/19531250000 : ℚ) : ℝ) ≤ stT162 250 := by
  have hc : ((-13617/15625 : ℚ) : ℝ)
      ≤ Real.cos (((162 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st162_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1076519169/19531250000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-13617/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st162_p1 : ((93423/100000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT162 (i+1) := by
  rw [Finset.sum_range_one]
  exact st162_t1

theorem st162_p2 : ((1966330167377/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT162 (i+1))
      = (∑ i ∈ Finset.range 1, stT162 (i+1)) + stT162 2 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 1
    simpa using h
  have hprev := st162_p1
  have hstep := st162_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p3 : ((11432066282911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT162 (i+1))
      = (∑ i ∈ Finset.range 2, stT162 (i+1)) + stT162 3 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 2
    simpa using h
  have hprev := st162_p2
  have hstep := st162_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p4 : ((13006421282911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT162 (i+1))
      = (∑ i ∈ Finset.range 3, stT162 (i+1)) + stT162 4 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 3
    simpa using h
  have hprev := st162_p3
  have hstep := st162_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p5 : ((8792045785543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT162 (i+1))
      = (∑ i ∈ Finset.range 4, stT162 (i+1)) + stT162 5 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 4
    simpa using h
  have hprev := st162_p4
  have hstep := st162_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p6 : ((8660108099949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT162 (i+1))
      = (∑ i ∈ Finset.range 5, stT162 (i+1)) + stT162 6 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 5
    simpa using h
  have hprev := st162_p5
  have hstep := st162_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p7 : ((9142598554769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT162 (i+1))
      = (∑ i ∈ Finset.range 6, stT162 (i+1)) + stT162 7 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 6
    simpa using h
  have hprev := st162_p6
  have hstep := st162_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p8 : ((7487512558883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT162 (i+1))
      = (∑ i ∈ Finset.range 7, stT162 (i+1)) + stT162 8 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 7
    simpa using h
  have hprev := st162_p7
  have hstep := st162_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p9 : ((6643862390153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT162 (i+1))
      = (∑ i ∈ Finset.range 8, stT162 (i+1)) + stT162 9 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 8
    simpa using h
  have hprev := st162_p8
  have hstep := st162_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p10 : ((3818872961633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT162 (i+1))
      = (∑ i ∈ Finset.range 9, stT162 (i+1)) + stT162 10 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 9
    simpa using h
  have hprev := st162_p9
  have hstep := st162_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p11 : ((3028828840753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT162 (i+1))
      = (∑ i ∈ Finset.range 10, stT162 (i+1)) + stT162 11 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 10
    simpa using h
  have hprev := st162_p10
  have hstep := st162_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p12 : ((4038931883163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT162 (i+1))
      = (∑ i ∈ Finset.range 11, stT162 (i+1)) + stT162 12 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 11
    simpa using h
  have hprev := st162_p11
  have hstep := st162_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p13 : ((4546363122663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT162 (i+1))
      = (∑ i ∈ Finset.range 12, stT162 (i+1)) + stT162 13 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 12
    simpa using h
  have hprev := st162_p12
  have hstep := st162_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p14 : ((1124383681099/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT162 (i+1))
      = (∑ i ∈ Finset.range 13, stT162 (i+1)) + stT162 14 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 13
    simpa using h
  have hprev := st162_p13
  have hstep := st162_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p15 : ((6562695426157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT162 (i+1))
      = (∑ i ∈ Finset.range 14, stT162 (i+1)) + stT162 15 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 14
    simpa using h
  have hprev := st162_p14
  have hstep := st162_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p16 : ((10720012390163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT162 (i+1))
      = (∑ i ∈ Finset.range 15, stT162 (i+1)) + stT162 16 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 15
    simpa using h
  have hprev := st162_p15
  have hstep := st162_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p17 : ((12617016712343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT162 (i+1))
      = (∑ i ∈ Finset.range 16, stT162 (i+1)) + stT162 17 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 16
    simpa using h
  have hprev := st162_p16
  have hstep := st162_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p18 : ((527846455643/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT162 (i+1))
      = (∑ i ∈ Finset.range 17, stT162 (i+1)) + stT162 18 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 17
    simpa using h
  have hprev := st162_p17
  have hstep := st162_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p19 : ((12822246265213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT162 (i+1))
      = (∑ i ∈ Finset.range 18, stT162 (i+1)) + stT162 19 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 18
    simpa using h
  have hprev := st162_p18
  have hstep := st162_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p20 : ((12167480833453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT162 (i+1))
      = (∑ i ∈ Finset.range 19, stT162 (i+1)) + stT162 20 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 19
    simpa using h
  have hprev := st162_p19
  have hstep := st162_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p21 : ((2528842653187/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT162 (i+1))
      = (∑ i ∈ Finset.range 20, stT162 (i+1)) + stT162 21 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 20
    simpa using h
  have hprev := st162_p20
  have hstep := st162_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p22 : ((10177959942247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT162 (i+1))
      = (∑ i ∈ Finset.range 21, stT162 (i+1)) + stT162 22 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 21
    simpa using h
  have hprev := st162_p21
  have hstep := st162_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p23 : ((11870807035231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT162 (i+1))
      = (∑ i ∈ Finset.range 22, stT162 (i+1)) + stT162 23 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 22
    simpa using h
  have hprev := st162_p22
  have hstep := st162_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p24 : ((1391180104507/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT162 (i+1))
      = (∑ i ∈ Finset.range 23, stT162 (i+1)) + stT162 24 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 23
    simpa using h
  have hprev := st162_p23
  have hstep := st162_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p25 : ((1581138304507/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT162 (i+1))
      = (∑ i ∈ Finset.range 24, stT162 (i+1)) + stT162 25 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 24
    simpa using h
  have hprev := st162_p24
  have hstep := st162_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p26 : ((8813097183303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT162 (i+1))
      = (∑ i ∈ Finset.range 25, stT162 (i+1)) + stT162 26 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 25
    simpa using h
  have hprev := st162_p25
  have hstep := st162_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p27 : ((9752235862803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT162 (i+1))
      = (∑ i ∈ Finset.range 26, stT162 (i+1)) + stT162 27 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 26
    simpa using h
  have hprev := st162_p26
  have hstep := st162_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p28 : ((10683118714097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT162 (i+1))
      = (∑ i ∈ Finset.range 27, stT162 (i+1)) + stT162 28 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 27
    simpa using h
  have hprev := st162_p27
  have hstep := st162_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p29 : ((22698454506407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT162 (i+1))
      = (∑ i ∈ Finset.range 28, stT162 (i+1)) + stT162 29 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 28
    simpa using h
  have hprev := st162_p28
  have hstep := st162_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p30 : ((56787092201/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT162 (i+1))
      = (∑ i ∈ Finset.range 29, stT162 (i+1)) + stT162 30 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 29
    simpa using h
  have hprev := st162_p29
  have hstep := st162_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p31 : ((106205872867/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT162 (i+1))
      = (∑ i ∈ Finset.range 30, stT162 (i+1)) + stT162 31 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 30
    simpa using h
  have hprev := st162_p30
  have hstep := st162_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p32 : ((9858502933/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT162 (i+1))
      = (∑ i ∈ Finset.range 31, stT162 (i+1)) + stT162 32 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 31
    simpa using h
  have hprev := st162_p31
  have hstep := st162_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p33 : ((630069694291/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT162 (i+1))
      = (∑ i ∈ Finset.range 32, stT162 (i+1)) + stT162 33 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 32
    simpa using h
  have hprev := st162_p32
  have hstep := st162_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p34 : ((10930775272161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT162 (i+1))
      = (∑ i ∈ Finset.range 33, stT162 (i+1)) + stT162 34 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 33
    simpa using h
  have hprev := st162_p33
  have hstep := st162_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p35 : ((135041807087/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT162 (i+1))
      = (∑ i ∈ Finset.range 34, stT162 (i+1)) + stT162 35 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 34
    simpa using h
  have hprev := st162_p34
  have hstep := st162_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p36 : ((2501797768599/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT162 (i+1))
      = (∑ i ∈ Finset.range 35, stT162 (i+1)) + stT162 36 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 35
    simpa using h
  have hprev := st162_p35
  have hstep := st162_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p37 : ((20906645670619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT162 (i+1))
      = (∑ i ∈ Finset.range 36, stT162 (i+1)) + stT162 37 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 36
    simpa using h
  have hprev := st162_p36
  have hstep := st162_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p38 : ((21829080350797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT162 (i+1))
      = (∑ i ∈ Finset.range 37, stT162 (i+1)) + stT162 38 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 37
    simpa using h
  have hprev := st162_p37
  have hstep := st162_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p39 : ((20235804760797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT162 (i+1))
      = (∑ i ∈ Finset.range 38, stT162 (i+1)) + stT162 39 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 38
    simpa using h
  have hprev := st162_p38
  have hstep := st162_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p40 : ((21008106873483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT162 (i+1))
      = (∑ i ∈ Finset.range 39, stT162 (i+1)) + stT162 40 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 39
    simpa using h
  have hprev := st162_p39
  have hstep := st162_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p41 : ((4308193058187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT162 (i+1))
      = (∑ i ∈ Finset.range 40, stT162 (i+1)) + stT162 41 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 40
    simpa using h
  have hprev := st162_p40
  have hstep := st162_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p42 : ((20158479349533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT162 (i+1))
      = (∑ i ∈ Finset.range 41, stT162 (i+1)) + stT162 42 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 41
    simpa using h
  have hprev := st162_p41
  have hstep := st162_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p43 : ((21649881129863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT162 (i+1))
      = (∑ i ∈ Finset.range 42, stT162 (i+1)) + stT162 43 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 42
    simpa using h
  have hprev := st162_p42
  have hstep := st162_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p44 : ((20591633403029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT162 (i+1))
      = (∑ i ∈ Finset.range 43, stT162 (i+1)) + stT162 44 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 43
    simpa using h
  have hprev := st162_p43
  have hstep := st162_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p45 : ((21002202045227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT162 (i+1))
      = (∑ i ∈ Finset.range 44, stT162 (i+1)) + stT162 45 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 44
    simpa using h
  have hprev := st162_p44
  have hstep := st162_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p46 : ((530193659369/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT162 (i+1))
      = (∑ i ∈ Finset.range 45, stT162 (i+1)) + stT162 46 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 45
    simpa using h
  have hprev := st162_p45
  have hstep := st162_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p47 : ((513276820129/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT162 (i+1))
      = (∑ i ∈ Finset.range 46, stT162 (i+1)) + stT162 47 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 46
    simpa using h
  have hprev := st162_p46
  have hstep := st162_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p48 : ((1075816895033/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT162 (i+1))
      = (∑ i ∈ Finset.range 47, stT162 (i+1)) + stT162 48 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 47
    simpa using h
  have hprev := st162_p47
  have hstep := st162_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p49 : ((2544268429473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT162 (i+1))
      = (∑ i ∈ Finset.range 48, stT162 (i+1)) + stT162 49 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 48
    simpa using h
  have hprev := st162_p48
  have hstep := st162_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p50 : ((5400567401053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT162 (i+1))
      = (∑ i ∈ Finset.range 49, stT162 (i+1)) + stT162 50 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 49
    simpa using h
  have hprev := st162_p49
  have hstep := st162_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p51 : ((2540666369477/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT162 (i+1))
      = (∑ i ∈ Finset.range 50, stT162 (i+1)) + stT162 51 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 50
    simpa using h
  have hprev := st162_p50
  have hstep := st162_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p52 : ((10796068394033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT162 (i+1))
      = (∑ i ∈ Finset.range 51, stT162 (i+1)) + stT162 52 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 51
    simpa using h
  have hprev := st162_p51
  have hstep := st162_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p53 : ((10185150257503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT162 (i+1))
      = (∑ i ∈ Finset.range 52, stT162 (i+1)) + stT162 53 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 52
    simpa using h
  have hprev := st162_p52
  have hstep := st162_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p54 : ((134390185319/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT162 (i+1))
      = (∑ i ∈ Finset.range 53, stT162 (i+1)) + stT162 54 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 53
    simpa using h
  have hprev := st162_p53
  have hstep := st162_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p55 : ((256529330743/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT162 (i+1))
      = (∑ i ∈ Finset.range 54, stT162 (i+1)) + stT162 55 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 54
    simpa using h
  have hprev := st162_p54
  have hstep := st162_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p56 : ((10633459395331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT162 (i+1))
      = (∑ i ∈ Finset.range 55, stT162 (i+1)) + stT162 56 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 55
    simpa using h
  have hprev := st162_p55
  have hstep := st162_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p57 : ((20854227421187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT162 (i+1))
      = (∑ i ∈ Finset.range 56, stT162 (i+1)) + stT162 57 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 56
    simpa using h
  have hprev := st162_p56
  have hstep := st162_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p58 : ((20844544879877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT162 (i+1))
      = (∑ i ∈ Finset.range 57, stT162 (i+1)) + stT162 58 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 57
    simpa using h
  have hprev := st162_p57
  have hstep := st162_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p59 : ((10663461047023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT162 (i+1))
      = (∑ i ∈ Finset.range 58, stT162 (i+1)) + stT162 59 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 58
    simpa using h
  have hprev := st162_p58
  have hstep := st162_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p60 : ((20402134608731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT162 (i+1))
      = (∑ i ∈ Finset.range 59, stT162 (i+1)) + stT162 60 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 59
    simpa using h
  have hprev := st162_p59
  have hstep := st162_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p61 : ((21621998818891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT162 (i+1))
      = (∑ i ∈ Finset.range 60, stT162 (i+1)) + stT162 61 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 60
    simpa using h
  have hprev := st162_p60
  have hstep := st162_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p62 : ((815078957929/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT162 (i+1))
      = (∑ i ∈ Finset.range 61, stT162 (i+1)) + stT162 62 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 61
    simpa using h
  have hprev := st162_p61
  have hstep := st162_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p63 : ((2130009505633/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT162 (i+1))
      = (∑ i ∈ Finset.range 62, stT162 (i+1)) + stT162 63 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 62
    simpa using h
  have hprev := st162_p62
  have hstep := st162_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p64 : ((21012636076363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT162 (i+1))
      = (∑ i ∈ Finset.range 63, stT162 (i+1)) + stT162 64 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 63
    simpa using h
  have hprev := st162_p63
  have hstep := st162_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p65 : ((4106387593723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT162 (i+1))
      = (∑ i ∈ Finset.range 64, stT162 (i+1)) + stT162 65 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 64
    simpa using h
  have hprev := st162_p64
  have hstep := st162_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p66 : ((21609368071041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT162 (i+1))
      = (∑ i ∈ Finset.range 65, stT162 (i+1)) + stT162 66 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 65
    simpa using h
  have hprev := st162_p65
  have hstep := st162_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p67 : ((1275760427131/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT162 (i+1))
      = (∑ i ∈ Finset.range 66, stT162 (i+1)) + stT162 67 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 66
    simpa using h
  have hprev := st162_p66
  have hstep := st162_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p68 : ((5281248984997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT162 (i+1))
      = (∑ i ∈ Finset.range 67, stT162 (i+1)) + stT162 68 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 67
    simpa using h
  have hprev := st162_p67
  have hstep := st162_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p69 : ((2130266009977/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT162 (i+1))
      = (∑ i ∈ Finset.range 68, stT162 (i+1)) + stT162 69 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 68
    simpa using h
  have hprev := st162_p68
  have hstep := st162_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p70 : ((20324306597049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT162 (i+1))
      = (∑ i ∈ Finset.range 69, stT162 (i+1)) + stT162 70 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 69
    simpa using h
  have hprev := st162_p69
  have hstep := st162_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p71 : ((1073965932823/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT162 (i+1))
      = (∑ i ∈ Finset.range 70, stT162 (i+1)) + stT162 71 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 70
    simpa using h
  have hprev := st162_p70
  have hstep := st162_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p72 : ((5238145090259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT162 (i+1))
      = (∑ i ∈ Finset.range 71, stT162 (i+1)) + stT162 72 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 71
    simpa using h
  have hprev := st162_p71
  have hstep := st162_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p73 : ((1278124974761/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT162 (i+1))
      = (∑ i ∈ Finset.range 72, stT162 (i+1)) + stT162 73 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 72
    simpa using h
  have hprev := st162_p72
  have hstep := st162_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p74 : ((5397900253661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT162 (i+1))
      = (∑ i ∈ Finset.range 73, stT162 (i+1)) + stT162 74 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 73
    simpa using h
  have hprev := st162_p73
  have hstep := st162_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p75 : ((20768637529037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT162 (i+1))
      = (∑ i ∈ Finset.range 74, stT162 (i+1)) + stT162 75 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 74
    simpa using h
  have hprev := st162_p74
  have hstep := st162_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p76 : ((641805548643/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT162 (i+1))
      = (∑ i ∈ Finset.range 75, stT162 (i+1)) + stT162 76 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 75
    simpa using h
  have hprev := st162_p75
  have hstep := st162_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p77 : ((21610447856901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT162 (i+1))
      = (∑ i ∈ Finset.range 76, stT162 (i+1)) + stT162 77 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 76
    simpa using h
  have hprev := st162_p76
  have hstep := st162_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p78 : ((20749468194813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT162 (i+1))
      = (∑ i ∈ Finset.range 77, stT162 (i+1)) + stT162 78 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 77
    simpa using h
  have hprev := st162_p77
  have hstep := st162_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p79 : ((20510444374301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT162 (i+1))
      = (∑ i ∈ Finset.range 78, stT162 (i+1)) + stT162 79 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 78
    simpa using h
  have hprev := st162_p78
  have hstep := st162_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p80 : ((1349552923789/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT162 (i+1))
      = (∑ i ∈ Finset.range 79, stT162 (i+1)) + stT162 80 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 79
    simpa using h
  have hprev := st162_p79
  have hstep := st162_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p81 : ((1305100110449/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT162 (i+1))
      = (∑ i ∈ Finset.range 80, stT162 (i+1)) + stT162 81 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 80
    simpa using h
  have hprev := st162_p80
  have hstep := st162_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p82 : ((5098008271279/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT162 (i+1))
      = (∑ i ∈ Finset.range 81, stT162 (i+1)) + stT162 82 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 81
    simpa using h
  have hprev := st162_p81
  have hstep := st162_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p83 : ((5371800798833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT162 (i+1))
      = (∑ i ∈ Finset.range 82, stT162 (i+1)) + stT162 83 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 82
    simpa using h
  have hprev := st162_p82
  have hstep := st162_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p84 : ((5290405484833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT162 (i+1))
      = (∑ i ∈ Finset.range 83, stT162 (i+1)) + stT162 84 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 83
    simpa using h
  have hprev := st162_p83
  have hstep := st162_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p85 : ((5074416363637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT162 (i+1))
      = (∑ i ∈ Finset.range 84, stT162 (i+1)) + stT162 85 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 84
    simpa using h
  have hprev := st162_p84
  have hstep := st162_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p86 : ((21189117307121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT162 (i+1))
      = (∑ i ∈ Finset.range 85, stT162 (i+1)) + stT162 86 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 85
    simpa using h
  have hprev := st162_p85
  have hstep := st162_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p87 : ((21501203749761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT162 (i+1))
      = (∑ i ∈ Finset.range 86, stT162 (i+1)) + stT162 87 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 86
    simpa using h
  have hprev := st162_p86
  have hstep := st162_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p88 : ((20435262643997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT162 (i+1))
      = (∑ i ∈ Finset.range 87, stT162 (i+1)) + stT162 88 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 87
    simpa using h
  have hprev := st162_p87
  have hstep := st162_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p89 : ((20692269516617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT162 (i+1))
      = (∑ i ∈ Finset.range 88, stT162 (i+1)) + stT162 89 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 88
    simpa using h
  have hprev := st162_p88
  have hstep := st162_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p90 : ((21625123017053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT162 (i+1))
      = (∑ i ∈ Finset.range 89, stT162 (i+1)) + stT162 90 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 89
    simpa using h
  have hprev := st162_p89
  have hstep := st162_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p91 : ((20946937132873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT162 (i+1))
      = (∑ i ∈ Finset.range 90, stT162 (i+1)) + stT162 91 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 90
    simpa using h
  have hprev := st162_p90
  have hstep := st162_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p92 : ((10150721849259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT162 (i+1))
      = (∑ i ∈ Finset.range 91, stT162 (i+1)) + stT162 92 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 91
    simpa using h
  have hprev := st162_p91
  have hstep := st162_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p93 : ((4243556763371/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT162 (i+1))
      = (∑ i ∈ Finset.range 92, stT162 (i+1)) + stT162 93 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 92
    simpa using h
  have hprev := st162_p92
  have hstep := st162_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p94 : ((2154723515557/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT162 (i+1))
      = (∑ i ∈ Finset.range 93, stT162 (i+1)) + stT162 94 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 93
    simpa using h
  have hprev := st162_p93
  have hstep := st162_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p95 : ((4107617468213/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT162 (i+1))
      = (∑ i ∈ Finset.range 94, stT162 (i+1)) + stT162 95 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 94
    simpa using h
  have hprev := st162_p94
  have hstep := st162_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p96 : ((10240401473099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT162 (i+1))
      = (∑ i ∈ Finset.range 95, stT162 (i+1)) + stT162 96 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 95
    simpa using h
  have hprev := st162_p95
  have hstep := st162_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p97 : ((671710391829/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT162 (i+1))
      = (∑ i ∈ Finset.range 96, stT162 (i+1)) + stT162 97 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 96
    simpa using h
  have hprev := st162_p96
  have hstep := st162_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p98 : ((10675547421423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT162 (i+1))
      = (∑ i ∈ Finset.range 97, stT162 (i+1)) + stT162 98 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 97
    simpa using h
  have hprev := st162_p97
  have hstep := st162_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p99 : ((2546184152901/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT162 (i+1))
      = (∑ i ∈ Finset.range 98, stT162 (i+1)) + stT162 99 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 98
    simpa using h
  have hprev := st162_p98
  have hstep := st162_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p100 : ((20639883952797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT162 (i+1))
      = (∑ i ∈ Finset.range 99, stT162 (i+1)) + stT162 100 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 99
    simpa using h
  have hprev := st162_p99
  have hstep := st162_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p101 : ((4317179891991/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT162 (i+1))
      = (∑ i ∈ Finset.range 100, stT162 (i+1)) + stT162 101 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 100
    simpa using h
  have hprev := st162_p100
  have hstep := st162_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p102 : ((21255352412227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT162 (i+1))
      = (∑ i ∈ Finset.range 101, stT162 (i+1)) + stT162 102 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 101
    simpa using h
  have hprev := st162_p101
  have hstep := st162_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p103 : ((20329713703627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT162 (i+1))
      = (∑ i ∈ Finset.range 102, stT162 (i+1)) + stT162 103 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 102
    simpa using h
  have hprev := st162_p102
  have hstep := st162_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p104 : ((20660777123227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT162 (i+1))
      = (∑ i ∈ Finset.range 103, stT162 (i+1)) + stT162 104 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 103
    simpa using h
  have hprev := st162_p103
  have hstep := st162_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p105 : ((21585882504127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT162 (i+1))
      = (∑ i ∈ Finset.range 104, stT162 (i+1)) + stT162 105 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 104
    simpa using h
  have hprev := st162_p104
  have hstep := st162_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p106 : ((21309343781923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT162 (i+1))
      = (∑ i ∈ Finset.range 105, stT162 (i+1)) + stT162 106 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 105
    simpa using h
  have hprev := st162_p105
  have hstep := st162_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p107 : ((4074007782207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT162 (i+1))
      = (∑ i ∈ Finset.range 106, stT162 (i+1)) + stT162 107 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 106
    simpa using h
  have hprev := st162_p106
  have hstep := st162_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p108 : ((4107543156957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT162 (i+1))
      = (∑ i ∈ Finset.range 107, stT162 (i+1)) + stT162 108 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 107
    simpa using h
  have hprev := st162_p107
  have hstep := st162_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p109 : ((21490945177811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT162 (i+1))
      = (∑ i ∈ Finset.range 108, stT162 (i+1)) + stT162 109 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 108
    simpa using h
  have hprev := st162_p108
  have hstep := st162_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p110 : ((10742511609559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT162 (i+1))
      = (∑ i ∈ Finset.range 109, stT162 (i+1)) + stT162 110 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 109
    simpa using h
  have hprev := st162_p109
  have hstep := st162_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p111 : ((10270211537917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT162 (i+1))
      = (∑ i ∈ Finset.range 110, stT162 (i+1)) + stT162 111 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 110
    simpa using h
  have hprev := st162_p110
  have hstep := st162_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p112 : ((10168728461573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT162 (i+1))
      = (∑ i ∈ Finset.range 111, stT162 (i+1)) + stT162 112 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 111
    simpa using h
  have hprev := st162_p111
  have hstep := st162_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p113 : ((10610996210573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT162 (i+1))
      = (∑ i ∈ Finset.range 112, stT162 (i+1)) + stT162 113 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 112
    simpa using h
  have hprev := st162_p112
  have hstep := st162_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p114 : ((5415824540239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT162 (i+1))
      = (∑ i ∈ Finset.range 113, stT162 (i+1)) + stT162 114 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 113
    simpa using h
  have hprev := st162_p113
  have hstep := st162_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p115 : ((10459500322553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT162 (i+1))
      = (∑ i ∈ Finset.range 114, stT162 (i+1)) + stT162 115 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 114
    simpa using h
  have hprev := st162_p114
  have hstep := st162_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p116 : ((253042336603/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT162 (i+1))
      = (∑ i ∈ Finset.range 115, stT162 (i+1)) + stT162 116 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 115
    simpa using h
  have hprev := st162_p115
  have hstep := st162_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p117 : ((1037334744887/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT162 (i+1))
      = (∑ i ∈ Finset.range 116, stT162 (i+1)) + stT162 117 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 116
    simpa using h
  have hprev := st162_p116
  have hstep := st162_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p118 : ((2700036221831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT162 (i+1))
      = (∑ i ∈ Finset.range 117, stT162 (i+1)) + stT162 118 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 117
    simpa using h
  have hprev := st162_p117
  have hstep := st162_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p119 : ((21436152068601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT162 (i+1))
      = (∑ i ∈ Finset.range 118, stT162 (i+1)) + stT162 119 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 118
    simpa using h
  have hprev := st162_p118
  have hstep := st162_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p120 : ((20523799579329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT162 (i+1))
      = (∑ i ∈ Finset.range 119, stT162 (i+1)) + stT162 120 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 119
    simpa using h
  have hprev := st162_p119
  have hstep := st162_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p121 : ((20288683192181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT162 (i+1))
      = (∑ i ∈ Finset.range 120, stT162 (i+1)) + stT162 121 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 120
    simpa using h
  have hprev := st162_p120
  have hstep := st162_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p122 : ((10541797393197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT162 (i+1))
      = (∑ i ∈ Finset.range 121, stT162 (i+1)) + stT162 122 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 121
    simpa using h
  have hprev := st162_p121
  have hstep := st162_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p123 : ((21696409613899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT162 (i+1))
      = (∑ i ∈ Finset.range 122, stT162 (i+1)) + stT162 123 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 122
    simpa using h
  have hprev := st162_p122
  have hstep := st162_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p124 : ((10608000994003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT162 (i+1))
      = (∑ i ∈ Finset.range 123, stT162 (i+1)) + stT162 124 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 123
    simpa using h
  have hprev := st162_p123
  have hstep := st162_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p125 : ((10180059681333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT162 (i+1))
      = (∑ i ∈ Finset.range 124, stT162 (i+1)) + stT162 125 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 124
    simpa using h
  have hprev := st162_p124
  have hstep := st162_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p126 : ((2546665368367/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT162 (i+1))
      = (∑ i ∈ Finset.range 125, stT162 (i+1)) + stT162 126 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 125
    simpa using h
  have hprev := st162_p125
  have hstep := st162_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p127 : ((26534025377/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT162 (i+1))
      = (∑ i ∈ Finset.range 126, stT162 (i+1)) + stT162 127 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 126
    simpa using h
  have hprev := st162_p126
  have hstep := st162_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p128 : ((21708230314083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT162 (i+1))
      = (∑ i ∈ Finset.range 127, stT162 (i+1)) + stT162 128 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 127
    simpa using h
  have hprev := st162_p127
  have hstep := st162_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p129 : ((1057549951967/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT162 (i+1))
      = (∑ i ∈ Finset.range 128, stT162 (i+1)) + stT162 129 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 128
    simpa using h
  have hprev := st162_p128
  have hstep := st162_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p130 : ((813271809451/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT162 (i+1))
      = (∑ i ∈ Finset.range 129, stT162 (i+1)) + stT162 130 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 129
    simpa using h
  have hprev := st162_p129
  have hstep := st162_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p131 : ((20363181305067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT162 (i+1))
      = (∑ i ∈ Finset.range 130, stT162 (i+1)) + stT162 131 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 130
    simpa using h
  have hprev := st162_p130
  have hstep := st162_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p132 : ((21193909205459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT162 (i+1))
      = (∑ i ∈ Finset.range 131, stT162 (i+1)) + stT162 132 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 131
    simpa using h
  have hprev := st162_p131
  have hstep := st162_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p133 : ((21719332169791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT162 (i+1))
      = (∑ i ∈ Finset.range 132, stT162 (i+1)) + stT162 133 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 132
    simpa using h
  have hprev := st162_p132
  have hstep := st162_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p134 : ((4251722019847/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT162 (i+1))
      = (∑ i ∈ Finset.range 133, stT162 (i+1)) + stT162 134 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 133
    simpa using h
  have hprev := st162_p133
  have hstep := st162_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p135 : ((20414404697121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT162 (i+1))
      = (∑ i ∈ Finset.range 134, stT162 (i+1)) + stT162 135 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 134
    simpa using h
  have hprev := st162_p134
  have hstep := st162_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p136 : ((10130807010951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT162 (i+1))
      = (∑ i ∈ Finset.range 135, stT162 (i+1)) + stT162 136 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 135
    simpa using h
  have hprev := st162_p135
  have hstep := st162_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p137 : ((20984038650891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT162 (i+1))
      = (∑ i ∈ Finset.range 136, stT162 (i+1)) + stT162 137 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 136
    simpa using h
  have hprev := st162_p136
  have hstep := st162_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p138 : ((4335844053663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT162 (i+1))
      = (∑ i ∈ Finset.range 137, stT162 (i+1)) + stT162 138 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 137
    simpa using h
  have hprev := st162_p137
  have hstep := st162_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p139 : ((10749518467239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT162 (i+1))
      = (∑ i ∈ Finset.range 138, stT162 (i+1)) + stT162 139 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 138
    simpa using h
  have hprev := st162_p138
  have hstep := st162_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p140 : ((20669937344013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT162 (i+1))
      = (∑ i ∈ Finset.range 139, stT162 (i+1)) + stT162 140 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 139
    simpa using h
  have hprev := st162_p139
  have hstep := st162_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p141 : ((20185203074333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT162 (i+1))
      = (∑ i ∈ Finset.range 140, stT162 (i+1)) + stT162 141 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 140
    simpa using h
  have hprev := st162_p140
  have hstep := st162_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p142 : ((824422752719/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT162 (i+1))
      = (∑ i ∈ Finset.range 141, stT162 (i+1)) + stT162 142 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 141
    simpa using h
  have hprev := st162_p141
  have hstep := st162_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p143 : ((21442782640261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT162 (i+1))
      = (∑ i ∈ Finset.range 142, stT162 (i+1)) + stT162 143 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 142
    simpa using h
  have hprev := st162_p142
  have hstep := st162_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p144 : ((21723949194461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT162 (i+1))
      = (∑ i ∈ Finset.range 143, stT162 (i+1)) + stT162 144 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 143
    simpa using h
  have hprev := st162_p143
  have hstep := st162_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p145 : ((10570844894473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT162 (i+1))
      = (∑ i ∈ Finset.range 144, stT162 (i+1)) + stT162 145 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 144
    simpa using h
  have hprev := st162_p144
  have hstep := st162_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p146 : ((10177966256971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT162 (i+1))
      = (∑ i ∈ Finset.range 145, stT162 (i+1)) + stT162 146 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 145
    simpa using h
  have hprev := st162_p145
  have hstep := st162_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p147 : ((632385317221/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT162 (i+1))
      = (∑ i ∈ Finset.range 146, stT162 (i+1)) + stT162 147 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 146
    simpa using h
  have hprev := st162_p146
  have hstep := st162_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p148 : ((5226566692247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT162 (i+1))
      = (∑ i ∈ Finset.range 147, stT162 (i+1)) + stT162 148 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 147
    simpa using h
  have hprev := st162_p147
  have hstep := st162_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p149 : ((21635522447489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT162 (i+1))
      = (∑ i ∈ Finset.range 148, stT162 (i+1)) + stT162 149 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 148
    simpa using h
  have hprev := st162_p148
  have hstep := st162_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p150 : ((21647097911281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT162 (i+1))
      = (∑ i ∈ Finset.range 149, stT162 (i+1)) + stT162 150 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 149
    simpa using h
  have hprev := st162_p149
  have hstep := st162_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p151 : ((20936271123139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT162 (i+1))
      = (∑ i ∈ Finset.range 150, stT162 (i+1)) + stT162 151 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 150
    simpa using h
  have hprev := st162_p150
  have hstep := st162_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p152 : ((20249323480239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT162 (i+1))
      = (∑ i ∈ Finset.range 151, stT162 (i+1)) + stT162 152 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 151
    simpa using h
  have hprev := st162_p151
  have hstep := st162_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p153 : ((162331828743/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT162 (i+1))
      = (∑ i ∈ Finset.range 152, stT162 (i+1)) + stT162 153 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 152
    simpa using h
  have hprev := st162_p152
  have hstep := st162_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p154 : ((21012349225991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT162 (i+1))
      = (∑ i ∈ Finset.range 153, stT162 (i+1)) + stT162 154 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 153
    simpa using h
  have hprev := st162_p153
  have hstep := st162_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p155 : ((21681808165921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT162 (i+1))
      = (∑ i ∈ Finset.range 154, stT162 (i+1)) + stT162 155 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 154
    simpa using h
  have hprev := st162_p154
  have hstep := st162_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p156 : ((2704583803533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT162 (i+1))
      = (∑ i ∈ Finset.range 155, stT162 (i+1)) + stT162 156 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 155
    simpa using h
  have hprev := st162_p155
  have hstep := st162_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p157 : ((209284703709/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT162 (i+1))
      = (∑ i ∈ Finset.range 156, stT162 (i+1)) + stT162 157 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 156
    simpa using h
  have hprev := st162_p156
  have hstep := st162_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p158 : ((10124949189621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT162 (i+1))
      = (∑ i ∈ Finset.range 157, stT162 (i+1)) + stT162 158 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 157
    simpa using h
  have hprev := st162_p157
  have hstep := st162_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p159 : ((4050062628983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT162 (i+1))
      = (∑ i ∈ Finset.range 158, stT162 (i+1)) + stT162 159 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 158
    simpa using h
  have hprev := st162_p158
  have hstep := st162_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p160 : ((20922366364987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT162 (i+1))
      = (∑ i ∈ Finset.range 159, stT162 (i+1)) + stT162 160 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 159
    simpa using h
  have hprev := st162_p159
  have hstep := st162_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p161 : ((21630327154207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT162 (i+1))
      = (∑ i ∈ Finset.range 160, stT162 (i+1)) + stT162 161 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 160
    simpa using h
  have hprev := st162_p160
  have hstep := st162_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p162 : ((21718801903347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT162 (i+1))
      = (∑ i ∈ Finset.range 161, stT162 (i+1)) + stT162 162 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 161
    simpa using h
  have hprev := st162_p161
  have hstep := st162_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p163 : ((844522617699/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT162 (i+1))
      = (∑ i ∈ Finset.range 162, stT162 (i+1)) + stT162 163 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 162
    simpa using h
  have hprev := st162_p162
  have hstep := st162_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p164 : ((5091994160231/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT162 (i+1))
      = (∑ i ∈ Finset.range 163, stT162 (i+1)) + stT162 164 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 163
    simpa using h
  have hprev := st162_p163
  have hstep := st162_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p165 : ((2518918160149/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT162 (i+1))
      = (∑ i ∈ Finset.range 164, stT162 (i+1)) + stT162 165 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 164
    simpa using h
  have hprev := st162_p164
  have hstep := st162_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p166 : ((10324741115971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT162 (i+1))
      = (∑ i ∈ Finset.range 165, stT162 (i+1)) + stT162 166 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 165
    simpa using h
  have hprev := st162_p165
  have hstep := st162_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p167 : ((21419469391331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT162 (i+1))
      = (∑ i ∈ Finset.range 166, stT162 (i+1)) + stT162 167 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 166
    simpa using h
  have hprev := st162_p166
  have hstep := st162_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p168 : ((4358476175683/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT162 (i+1))
      = (∑ i ∈ Finset.range 167, stT162 (i+1)) + stT162 168 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 167
    simpa using h
  have hprev := st162_p167
  have hstep := st162_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p169 : ((21452979238133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT162 (i+1))
      = (∑ i ∈ Finset.range 168, stT162 (i+1)) + stT162 169 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 168
    simpa using h
  have hprev := st162_p168
  have hstep := st162_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p170 : ((20695546079153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT162 (i+1))
      = (∑ i ∈ Finset.range 169, stT162 (i+1)) + stT162 170 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 169
    simpa using h
  have hprev := st162_p169
  have hstep := st162_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p171 : ((20158353220753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT162 (i+1))
      = (∑ i ∈ Finset.range 170, stT162 (i+1)) + stT162 171 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 170
    simpa using h
  have hprev := st162_p170
  have hstep := st162_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p172 : ((4056833795141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT162 (i+1))
      = (∑ i ∈ Finset.range 171, stT162 (i+1)) + stT162 172 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 171
    simpa using h
  have hprev := st162_p171
  have hstep := st162_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p173 : ((2096339923157/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT162 (i+1))
      = (∑ i ∈ Finset.range 172, stT162 (i+1)) + stT162 173 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 172
    simpa using h
  have hprev := st162_p172
  have hstep := st162_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p174 : ((10819994025403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT162 (i+1))
      = (∑ i ∈ Finset.range 173, stT162 (i+1)) + stT162 174 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 173
    simpa using h
  have hprev := st162_p173
  have hstep := st162_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p175 : ((10885616135083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT162 (i+1))
      = (∑ i ∈ Finset.range 174, stT162 (i+1)) + stT162 175 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 174
    simpa using h
  have hprev := st162_p174
  have hstep := st162_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p176 : ((5314551440023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT162 (i+1))
      = (∑ i ∈ Finset.range 175, stT162 (i+1)) + stT162 176 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 175
    simpa using h
  have hprev := st162_p175
  have hstep := st162_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p177 : ((20509952446297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT162 (i+1))
      = (∑ i ∈ Finset.range 176, stT162 (i+1)) + stT162 177 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 176
    simpa using h
  have hprev := st162_p176
  have hstep := st162_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p178 : ((20110164070009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT162 (i+1))
      = (∑ i ∈ Finset.range 177, stT162 (i+1)) + stT162 178 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 177
    simpa using h
  have hprev := st162_p177
  have hstep := st162_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p179 : ((20362931638309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT162 (i+1))
      = (∑ i ∈ Finset.range 178, stT162 (i+1)) + stT162 179 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 178
    simpa using h
  have hprev := st162_p178
  have hstep := st162_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p180 : ((10534821854167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT162 (i+1))
      = (∑ i ∈ Finset.range 179, stT162 (i+1)) + stT162 180 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 179
    simpa using h
  have hprev := st162_p179
  have hstep := st162_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p181 : ((10846837349723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT162 (i+1))
      = (∑ i ∈ Finset.range 180, stT162 (i+1)) + stT162 181 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 180
    simpa using h
  have hprev := st162_p180
  have hstep := st162_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p182 : ((5442644820799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT162 (i+1))
      = (∑ i ∈ Finset.range 181, stT162 (i+1)) + stT162 182 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 181
    simpa using h
  have hprev := st162_p181
  have hstep := st162_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p183 : ((10624363125759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT162 (i+1))
      = (∑ i ∈ Finset.range 182, stT162 (i+1)) + stT162 183 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 182
    simpa using h
  have hprev := st162_p182
  have hstep := st162_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p184 : ((2564356884451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT162 (i+1))
      = (∑ i ∈ Finset.range 183, stT162 (i+1)) + stT162 184 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 183
    simpa using h
  have hprev := st162_p183
  have hstep := st162_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p185 : ((10050750513939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT162 (i+1))
      = (∑ i ∈ Finset.range 184, stT162 (i+1)) + stT162 185 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 184
    simpa using h
  have hprev := st162_p184
  have hstep := st162_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p186 : ((10150744703829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT162 (i+1))
      = (∑ i ∈ Finset.range 185, stT162 (i+1)) + stT162 186 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 185
    simpa using h
  have hprev := st162_p185
  have hstep := st162_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p187 : ((10483706373961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT162 (i+1))
      = (∑ i ∈ Finset.range 186, stT162 (i+1)) + stT162 187 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 186
    simpa using h
  have hprev := st162_p186
  have hstep := st162_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p188 : ((10813904533003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT162 (i+1))
      = (∑ i ∈ Finset.range 187, stT162 (i+1)) + stT162 188 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 187
    simpa using h
  have hprev := st162_p187
  have hstep := st162_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p189 : ((10912026440539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT162 (i+1))
      = (∑ i ∈ Finset.range 188, stT162 (i+1)) + stT162 189 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 188
    simpa using h
  have hprev := st162_p188
  have hstep := st162_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p190 : ((5356359885857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT162 (i+1))
      = (∑ i ∈ Finset.range 189, stT162 (i+1)) + stT162 190 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 189
    simpa using h
  have hprev := st162_p189
  have hstep := st162_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p191 : ((5177195480107/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT162 (i+1))
      = (∑ i ∈ Finset.range 190, stT162 (i+1)) + stT162 191 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 190
    simpa using h
  have hprev := st162_p190
  have hstep := st162_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p192 : ((5040032541359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT162 (i+1))
      = (∑ i ∈ Finset.range 191, stT162 (i+1)) + stT162 192 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 191
    simpa using h
  have hprev := st162_p191
  have hstep := st162_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p193 : ((1007211615463/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT162 (i+1))
      = (∑ i ∈ Finset.range 192, stT162 (i+1)) + stT162 193 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 192
    simpa using h
  have hprev := st162_p192
  have hstep := st162_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p194 : ((1291672544109/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT162 (i+1))
      = (∑ i ∈ Finset.range 193, stT162 (i+1)) + stT162 194 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 193
    simpa using h
  have hprev := st162_p193
  have hstep := st162_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p195 : ((10690350649877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT162 (i+1))
      = (∑ i ∈ Finset.range 194, stT162 (i+1)) + stT162 195 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 194
    simpa using h
  have hprev := st162_p194
  have hstep := st162_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p196 : ((10910671858127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT162 (i+1))
      = (∑ i ∈ Finset.range 195, stT162 (i+1)) + stT162 196 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 195
    simpa using h
  have hprev := st162_p195
  have hstep := st162_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p197 : ((1356756206293/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT162 (i+1))
      = (∑ i ∈ Finset.range 196, stT162 (i+1)) + stT162 197 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 196
    simpa using h
  have hprev := st162_p196
  have hstep := st162_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p198 : ((10558961344259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT162 (i+1))
      = (∑ i ∈ Finset.range 197, stT162 (i+1)) + stT162 198 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 197
    simpa using h
  have hprev := st162_p197
  have hstep := st162_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p199 : ((10213448713049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT162 (i+1))
      = (∑ i ∈ Finset.range 198, stT162 (i+1)) + stT162 199 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 198
    simpa using h
  have hprev := st162_p198
  have hstep := st162_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p200 : ((20067191388091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT162 (i+1))
      = (∑ i ∈ Finset.range 199, stT162 (i+1)) + stT162 200 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 199
    simpa using h
  have hprev := st162_p199
  have hstep := st162_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p201 : ((10129132910933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT162 (i+1))
      = (∑ i ∈ Finset.range 200, stT162 (i+1)) + stT162 201 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 200
    simpa using h
  have hprev := st162_p200
  have hstep := st162_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p202 : ((10439109605253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT162 (i+1))
      = (∑ i ∈ Finset.range 201, stT162 (i+1)) + stT162 202 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 201
    simpa using h
  have hprev := st162_p201
  have hstep := st162_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p203 : ((5386778863557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT162 (i+1))
      = (∑ i ∈ Finset.range 202, stT162 (i+1)) + stT162 203 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 202
    simpa using h
  have hprev := st162_p202
  have hstep := st162_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p204 : ((5465602025037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT162 (i+1))
      = (∑ i ∈ Finset.range 203, stT162 (i+1)) + stT162 204 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 203
    simpa using h
  have hprev := st162_p203
  have hstep := st162_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p205 : ((21639363461867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT162 (i+1))
      = (∑ i ∈ Finset.range 204, stT162 (i+1)) + stT162 205 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 204
    simpa using h
  have hprev := st162_p204
  have hstep := st162_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p206 : ((4202848235171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT162 (i+1))
      = (∑ i ∈ Finset.range 205, stT162 (i+1)) + stT162 206 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 205
    simpa using h
  have hprev := st162_p205
  have hstep := st162_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p207 : ((20355992240209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT162 (i+1))
      = (∑ i ∈ Finset.range 206, stT162 (i+1)) + stT162 207 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 206
    simpa using h
  have hprev := st162_p206
  have hstep := st162_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p208 : ((20046241766481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT162 (i+1))
      = (∑ i ∈ Finset.range 207, stT162 (i+1)) + stT162 208 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 207
    simpa using h
  have hprev := st162_p207
  have hstep := st162_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p209 : ((20259811230837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT162 (i+1))
      = (∑ i ∈ Finset.range 208, stT162 (i+1)) + stT162 209 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 208
    simpa using h
  have hprev := st162_p208
  have hstep := st162_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p210 : ((2608839255529/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT162 (i+1))
      = (∑ i ∈ Finset.range 209, stT162 (i+1)) + stT162 210 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 209
    simpa using h
  have hprev := st162_p209
  have hstep := st162_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p211 : ((5382785403047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT162 (i+1))
      = (∑ i ∈ Finset.range 210, stT162 (i+1)) + stT162 211 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 210
    simpa using h
  have hprev := st162_p210
  have hstep := st162_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p212 : ((10935834859711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT162 (i+1))
      = (∑ i ∈ Finset.range 211, stT162 (i+1)) + stT162 212 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 211
    simpa using h
  have hprev := st162_p211
  have hstep := st162_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p213 : ((868256825309/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT162 (i+1))
      = (∑ i ∈ Finset.range 212, stT162 (i+1)) + stT162 213 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 212
    simpa using h
  have hprev := st162_p212
  have hstep := st162_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p214 : ((21130315543091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT162 (i+1))
      = (∑ i ∈ Finset.range 213, stT162 (i+1)) + stT162 214 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 213
    simpa using h
  have hprev := st162_p213
  have hstep := st162_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p215 : ((5115036413599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT162 (i+1))
      = (∑ i ∈ Finset.range 214, stT162 (i+1)) + stT162 215 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 214
    simpa using h
  have hprev := st162_p214
  have hstep := st162_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p216 : ((10028995861297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT162 (i+1))
      = (∑ i ∈ Finset.range 215, stT162 (i+1)) + stT162 216 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 215
    simpa using h
  have hprev := st162_p215
  have hstep := st162_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p217 : ((10068254428083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT162 (i+1))
      = (∑ i ∈ Finset.range 216, stT162 (i+1)) + stT162 217 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 216
    simpa using h
  have hprev := st162_p216
  have hstep := st162_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p218 : ((2581262944207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT162 (i+1))
      = (∑ i ∈ Finset.range 217, stT162 (i+1)) + stT162 218 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 217
    simpa using h
  have hprev := st162_p217
  have hstep := st162_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p219 : ((2665684119091/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT162 (i+1))
      = (∑ i ∈ Finset.range 218, stT162 (i+1)) + stT162 219 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 218
    simpa using h
  have hprev := st162_p218
  have hstep := st162_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p220 : ((21809703574697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT162 (i+1))
      = (∑ i ∈ Finset.range 219, stT162 (i+1)) + stT162 220 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 219
    simpa using h
  have hprev := st162_p219
  have hstep := st162_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p221 : ((21854453752169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT162 (i+1))
      = (∑ i ∈ Finset.range 220, stT162 (i+1)) + stT162 221 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 220
    simpa using h
  have hprev := st162_p220
  have hstep := st162_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p222 : ((21440414314241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT162 (i+1))
      = (∑ i ∈ Finset.range 221, stT162 (i+1)) + stT162 222 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 221
    simpa using h
  have hprev := st162_p221
  have hstep := st162_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p223 : ((20781307283841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT162 (i+1))
      = (∑ i ∈ Finset.range 222, stT162 (i+1)) + stT162 223 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 222
    simpa using h
  have hprev := st162_p222
  have hstep := st162_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p224 : ((20210566796271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT162 (i+1))
      = (∑ i ∈ Finset.range 223, stT162 (i+1)) + stT162 224 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 223
    simpa using h
  have hprev := st162_p223
  have hstep := st162_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p225 : ((5003012174253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT162 (i+1))
      = (∑ i ∈ Finset.range 224, stT162 (i+1)) + stT162 225 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 224
    simpa using h
  have hprev := st162_p224
  have hstep := st162_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p226 : ((2535109324059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT162 (i+1))
      = (∑ i ∈ Finset.range 225, stT162 (i+1)) + stT162 226 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 225
    simpa using h
  have hprev := st162_p225
  have hstep := st162_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p227 : ((2088149479197/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT162 (i+1))
      = (∑ i ∈ Finset.range 226, stT162 (i+1)) + stT162 227 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 226
    simpa using h
  have hprev := st162_p226
  have hstep := st162_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p228 : ((2151927019529/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT162 (i+1))
      = (∑ i ∈ Finset.range 227, stT162 (i+1)) + stT162 228 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 227
    simpa using h
  have hprev := st162_p227
  have hstep := st162_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p229 : ((2188645371699/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT162 (i+1))
      = (∑ i ∈ Finset.range 228, stT162 (i+1)) + stT162 229 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 228
    simpa using h
  have hprev := st162_p228
  have hstep := st162_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p230 : ((10904829784103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT162 (i+1))
      = (∑ i ∈ Finset.range 229, stT162 (i+1)) + stT162 230 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 229
    simpa using h
  have hprev := st162_p229
  have hstep := st162_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p231 : ((10664396358599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT162 (i+1))
      = (∑ i ∈ Finset.range 230, stT162 (i+1)) + stT162 231 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 230
    simpa using h
  have hprev := st162_p230
  have hstep := st162_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p232 : ((20673098109839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT162 (i+1))
      = (∑ i ∈ Finset.range 231, stT162 (i+1)) + stT162 232 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 231
    simpa using h
  have hprev := st162_p231
  have hstep := st162_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p233 : ((20149658252327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT162 (i+1))
      = (∑ i ∈ Finset.range 232, stT162 (i+1)) + stT162 233 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 232
    simpa using h
  have hprev := st162_p232
  have hstep := st162_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p234 : ((19999482849323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT162 (i+1))
      = (∑ i ∈ Finset.range 233, stT162 (i+1)) + stT162 234 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 233
    simpa using h
  have hprev := st162_p233
  have hstep := st162_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p235 : ((20288517644219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT162 (i+1))
      = (∑ i ∈ Finset.range 234, stT162 (i+1)) + stT162 235 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 234
    simpa using h
  have hprev := st162_p234
  have hstep := st162_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p236 : ((20881840732283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT162 (i+1))
      = (∑ i ∈ Finset.range 235, stT162 (i+1)) + stT162 236 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 235
    simpa using h
  have hprev := st162_p235
  have hstep := st162_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p237 : ((21509347770767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT162 (i+1))
      = (∑ i ∈ Finset.range 236, stT162 (i+1)) + stT162 237 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 236
    simpa using h
  have hprev := st162_p236
  have hstep := st162_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p238 : ((875595947089/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT162 (i+1))
      = (∑ i ∈ Finset.range 237, stT162 (i+1)) + stT162 238 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 237
    simpa using h
  have hprev := st162_p237
  have hstep := st162_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p239 : ((4371283575301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT162 (i+1))
      = (∑ i ∈ Finset.range 238, stT162 (i+1)) + stT162 239 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 238
    simpa using h
  have hprev := st162_p238
  have hstep := st162_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p240 : ((21426814428581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT162 (i+1))
      = (∑ i ∈ Finset.range 239, stT162 (i+1)) + stT162 240 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 239
    simpa using h
  have hprev := st162_p239
  have hstep := st162_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p241 : ((10395903839383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT162 (i+1))
      = (∑ i ∈ Finset.range 240, stT162 (i+1)) + stT162 241 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 240
    simpa using h
  have hprev := st162_p240
  have hstep := st162_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p242 : ((20228185789841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT162 (i+1))
      = (∑ i ∈ Finset.range 241, stT162 (i+1)) + stT162 242 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 241
    simpa using h
  have hprev := st162_p241
  have hstep := st162_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p243 : ((1248609428497/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT162 (i+1))
      = (∑ i ∈ Finset.range 242, stT162 (i+1)) + stT162 243 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 242
    simpa using h
  have hprev := st162_p242
  have hstep := st162_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p244 : ((157382484017/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT162 (i+1))
      = (∑ i ∈ Finset.range 243, stT162 (i+1)) + stT162 244 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 243
    simpa using h
  have hprev := st162_p243
  have hstep := st162_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p245 : ((5163966293687/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT162 (i+1))
      = (∑ i ∈ Finset.range 244, stT162 (i+1)) + stT162 245 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 244
    simpa using h
  have hprev := st162_p244
  have hstep := st162_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p246 : ((5323332080949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT162 (i+1))
      = (∑ i ∈ Finset.range 245, stT162 (i+1)) + stT162 246 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 245
    simpa using h
  have hprev := st162_p245
  have hstep := st162_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p247 : ((5447694425033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT162 (i+1))
      = (∑ i ∈ Finset.range 246, stT162 (i+1)) + stT162 247 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 246
    simpa using h
  have hprev := st162_p246
  have hstep := st162_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p248 : ((5485897930033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT162 (i+1))
      = (∑ i ∈ Finset.range 247, stT162 (i+1)) + stT162 248 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 247
    simpa using h
  have hprev := st162_p247
  have hstep := st162_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p249 : ((1355727525277/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT162 (i+1))
      = (∑ i ∈ Finset.range 248, stT162 (i+1)) + stT162 249 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 248
    simpa using h
  have hprev := st162_p248
  have hstep := st162_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_p250 : ((1321278911869/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT162 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT162 (i+1))
      = (∑ i ∈ Finset.range 249, stT162 (i+1)) + stT162 250 := by
    have h := Finset.sum_range_succ (fun i => stT162 (i+1)) 249
    simpa using h
  have hprev := st162_p249
  have hstep := st162_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st162_s250 :
    |Real.sin (((162 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))
      - ((98101/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1643077/2500000) (δ := 4091/500000000) (ψ := -364563/1000000) 162 142
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 162`** (evaluated boundary). -/
theorem station_162_sign : 0 < hardyG ((((162:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 162 250 (by norm_num) (by norm_num)
    ((-364563/1000000 : ℚ) : ℝ)
  have hchain := st162_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT162 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((162 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-364563/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st162_c250
  have hsinb := abs_le.mp st162_s250
  have hbdy_lo : ((-781026001789/16402656250000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((162 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ))) / 2
          - ((((162:ℕ)):ℝ))
            * Real.sin (((162 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-364563/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((162:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((162:ℝ) * Real.log (250:ℝ) - ((-364563/1000000 : ℚ) : ℝ))) / 2
        - ((162:ℝ)) * Real.sin ((162:ℝ) * Real.log (250:ℝ) - ((-364563/1000000 : ℚ) : ℝ))
        ≥ ((-9879277/125000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((162:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-9879277/125000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-9879277/125000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-9879277/125000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((162:ℕ)):ℝ))+1) * (((((162:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((280577166793/468750000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1321278911869/625000000000 : ℚ) : ℝ) + ((-781026001789/16402656250000 : ℚ) : ℝ)
      - ((280577166793/468750000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-364563/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((162:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-364563/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((162:ℕ)):ℝ)))).re
      - Real.sin ((-364563/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((162:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((162:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((162:ℕ)):ℝ))
      = (((((162:ℕ)):ℝ)) * (Real.log ((((162:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((162:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_162
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
  have hθwin : |(((-364563/1000000 : ℚ) : ℝ) + ((29:ℤ)) * (2*Real.pi)) - theta ((((162:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((162:ℕ)):ℝ)))
    (φ := ((-364563/1000000 : ℚ) : ℝ) + ((29:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-364563/1000000 : ℚ)) : ℝ) 29).1,
    (cos_sin_shift (((-364563/1000000 : ℚ)) : ℝ) 29).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_162_sign
end AxiomAudit
