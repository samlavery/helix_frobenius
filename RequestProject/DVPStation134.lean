import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 134` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT134 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((134 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))

theorem st134_c1 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((829813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 740029/5000000) (δ := 201/1000000000) (ψ := -592023/1000000) 134 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t1 : ((829763/1000000 : ℚ) : ℝ) ≤ stT134 1 := by
  have hc : ((829763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((829763/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((829763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c2 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((357547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241887/1250000) (δ := 6809/1000000000) (ψ := -592023/1000000) 134 15
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t2 : ((1264031007987/2500000000000 : ℚ) : ℝ) ≤ stT134 2 := by
  have hc : ((178761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1264031007987/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((178761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c3 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-98859/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7475957/10000000) (δ := 3387/500000000) (ψ := -592023/1000000) 134 24
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t3 : ((-35674475037/62500000000 : ℚ) : ℝ) ≤ stT134 3 := by
  have hc : ((-6179/6250 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35674475037/62500000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-6179/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c4 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-3369/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5350233/10000000) (δ := 6817/1000000000) (ψ := -592023/1000000) 134 30
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t4 : ((-269545053909/1000000000000 : ℚ) : ℝ) ≤ stT134 4 := by
  have hc : ((-53909/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269545053909/1000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-53909/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c5 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-174237/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328551/500000) (δ := 3423/500000000) (ψ := -592023/1000000) 134 34
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t5 : ((-97407035199/250000000000 : ℚ) : ℝ) ≤ stT134 5 := by
  have hc : ((-174247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97407035199/250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-174247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c6 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-174241/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4816869/10000000) (δ := 6729/1000000000) (ψ := -592023/1000000) 134 38
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t6 : ((-355718991239/2500000000000 : ℚ) : ℝ) ≤ stT134 6 := by
  have hc : ((-87133/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355718991239/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-87133/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c7 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-414971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12749/20000) (δ := 69/10000000) (ψ := -592023/1000000) 134 42
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t7 : ((-78426877821/250000000000 : ℚ) : ℝ) ≤ stT134 7 := by
  have hc : ((-103749/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78426877821/250000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-103749/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c8 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-467141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6942593/10000000) (δ := 6717/1000000000) (ψ := -592023/1000000) 134 44
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t8 : ((-412920319161/1250000000000 : ℚ) : ℝ) ≤ stT134 8 := by
  have hc : ((-233583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-412920319161/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-233583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c9 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((958359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90499/1250000) (δ := 1691/250000000) (ψ := -592023/1000000) 134 47
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t9 : ((3194363013897/10000000000000 : ℚ) : ℝ) ≤ stT134 9 := by
  have hc : ((958309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3194363013897/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((958309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c10 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((303589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3155849/10000000) (δ := 27/4000000) (ψ := -592023/1000000) 134 49
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t10 : ((959874398303/10000000000000 : ℚ) : ℝ) ≤ stT134 10 := by
  have hc : ((303539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((959874398303/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((303539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c11 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((103077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91721/250000) (δ := 1717/250000000) (ψ := -592023/1000000) 134 51
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t11 : ((310638047051/10000000000000 : ℚ) : ℝ) ≤ stT134 11 := by
  have hc : ((103027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310638047051/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((103027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c12 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((846887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350433/2500000) (δ := 6721/1000000000) (ψ := -592023/1000000) 134 53
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t12 : ((2444607556587/10000000000000 : ℚ) : ℝ) ≤ stT134 12 := by
  have hc : ((846837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2444607556587/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((846837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c13 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((286757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -319989/1000000) (δ := 6707/1000000000) (ψ := -592023/1000000) 134 55
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t13 : ((1590363729/20000000000 : ℚ) : ℝ) ≤ stT134 13 := by
  have hc : ((286707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1590363729/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((286707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c14 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-714937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5918327/10000000) (δ := 1701/250000000) (ψ := -592023/1000000) 134 56
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t14 : ((-1910883551031/10000000000000 : ℚ) : ℝ) ≤ stT134 14 := by
  have hc : ((-714987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1910883551031/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-714987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c15 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((9038/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1192489/5000000) (δ := 3409/500000000) (ψ := -592023/1000000) 134 58
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t15 : ((186671922927/1250000000000 : ℚ) : ℝ) ≤ stT134 15 := by
  have hc : ((289191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186671922927/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((289191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c16 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((31827/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110233/312500) (δ := 269/40000000) (ψ := -592023/1000000) 134 59
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t16 : ((31817/800000 : ℚ) : ℝ) ≤ stT134 16 := by
  have hc : ((31817/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31817/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((31817/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c17 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-993967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -757923/1000000) (δ := 429/62500000) (ψ := -592023/1000000) 134 61
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t17 : ((-2410846089069/10000000000000 : ℚ) : ℝ) ≤ stT134 17 := by
  have hc : ((-994017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2410846089069/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-994017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c18 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-84753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4139129/10000000) (δ := 1689/250000000) (ψ := -592023/1000000) 134 62
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t18 : ((-199882621469/10000000000000 : ℚ) : ℝ) ≤ stT134 18 := by
  have hc : ((-84803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199882621469/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-84803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c19 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((768801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86729/500000) (δ := 3377/500000000) (ψ := -592023/1000000) 134 63
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t19 : ((1763635487907/10000000000000 : ℚ) : ℝ) ≤ stT134 19 := by
  have hc : ((768751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1763635487907/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((768751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c20 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((497313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32411/1250000) (δ := 3371/500000000) (ψ := -592023/1000000) 134 64
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t20 : ((138996160787/625000000000 : ℚ) : ℝ) ≤ stT134 20 := by
  have hc : ((62161/62500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138996160787/625000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((62161/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c21 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((988623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188733/5000000) (δ := 423/62500000) (ψ := -592023/1000000) 134 65
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t21 : ((1078621125997/5000000000000 : ℚ) : ℝ) ≤ stT134 21 := by
  have hc : ((988573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1078621125997/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((988573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c22 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((198971/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253703/10000000) (δ := 11/1600000) (ψ := -592023/1000000) 134 66
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t22 : ((424186244727/2000000000000 : ℚ) : ℝ) ≤ stT134 22 := by
  have hc : ((198961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424186244727/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((198961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c23 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((487379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140727/2500000) (δ := 341/50000000) (ψ := -592023/1000000) 134 67
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t23 : ((63512704311/312500000000 : ℚ) : ℝ) ≤ stT134 23 := by
  have hc : ((243677/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63512704311/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((243677/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c24 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((13857/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402681/2000000) (δ := 6713/1000000000) (ψ := -592023/1000000) 134 68
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t24 : ((883857353/6250000000 : ℚ) : ℝ) ≤ stT134 24 := by
  have hc : ((433/625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((883857353/6250000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((433/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c25 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-9517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2022999/5000000) (δ := 6797/1000000000) (ψ := -592023/1000000) 134 69
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t25 : ((-19054009527/2000000000000 : ℚ) : ℝ) ≤ stT134 25 := by
  have hc : ((-9527/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19054009527/2000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-9527/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c26 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-219923/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6615027/10000000) (δ := 419/62500000) (ψ := -592023/1000000) 134 70
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t26 : ((-431329145051/2500000000000 : ℚ) : ℝ) ≤ stT134 26 := by
  have hc : ((-439871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431329145051/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-439871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c27 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-148981/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6027973/10000000) (δ := 6899/1000000000) (ψ := -592023/1000000) 134 70
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t27 : ((-286733328491/2000000000000 : ℚ) : ℝ) ≤ stT134 27 := by
  have hc : ((-148991/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286733328491/2000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-148991/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c28 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((134807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250319/1000000) (δ := 6811/1000000000) (ψ := -592023/1000000) 134 71
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t28 : ((254737611579/2500000000000 : ℚ) : ℝ) ≤ stT134 28 := by
  have hc : ((269589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254737611579/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((269589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c29 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((836641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362297/2500000) (δ := 3359/500000000) (ψ := -592023/1000000) 134 72
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t29 : ((1553510167223/10000000000000 : ℚ) : ℝ) ≤ stT134 29 := by
  have hc : ((836591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1553510167223/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((836591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c30 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-6811/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5800149/10000000) (δ := 6777/1000000000) (ψ := -592023/1000000) 134 73
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t30 : ((-12436041633/100000000000 : ℚ) : ℝ) ≤ stT134 30 := by
  have hc : ((-13623/20000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12436041633/100000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-13623/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c31 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-7532/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296117/2500000) (δ := 3413/500000000) (ψ := -592023/1000000) 134 73
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t31 : ((-216468510323/2500000000000 : ℚ) : ℝ) ≤ stT134 31 := by
  have hc : ((-241049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216468510323/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-241049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c32 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((998991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 112319/10000000) (δ := 6733/1000000000) (ψ := -592023/1000000) 134 74
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t32 : ((882946967903/5000000000000 : ℚ) : ℝ) ≤ stT134 32 := by
  have hc : ((998941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((882946967903/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((998941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c33 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-25881/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2643579/5000000) (δ := 171/25000000) (ψ := -592023/1000000) 134 75
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t33 : ((-90114802959/1000000000000 : ℚ) : ℝ) ≤ stT134 33 := by
  have hc : ((-51767/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90114802959/1000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-51767/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c34 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-309477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4713597/10000000) (δ := 171/25000000) (ψ := -592023/1000000) 134 75
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t34 : ((-265417235811/5000000000000 : ℚ) : ℝ) ≤ stT134 34 := by
  have hc : ((-309527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265417235811/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-309527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c35 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((871069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641777/5000000) (δ := 6747/1000000000) (ψ := -592023/1000000) 134 76
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t35 : ((368072595963/2500000000000 : ℚ) : ℝ) ≤ stT134 35 := by
  have hc : ((871019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368072595963/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((871019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c36 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-496411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3777133/5000000) (δ := 6749/1000000000) (ψ := -592023/1000000) 134 77
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t36 : ((-206848374703/1250000000000 : ℚ) : ℝ) ≤ stT134 36 := by
  have hc : ((-124109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206848374703/1250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-124109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c37 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((796229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1624399/10000000) (δ := 6749/1000000000) (ψ := -592023/1000000) 134 77
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t37 : ((1308909518031/10000000000000 : ℚ) : ℝ) ≤ stT134 37 := by
  have hc : ((796179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1308909518031/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((796179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c38 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-469823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5149717/10000000) (δ := 3381/500000000) (ψ := -592023/1000000) 134 78
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t38 : ((-152447005739/2000000000000 : ℚ) : ℝ) ≤ stT134 38 := by
  have hc : ((-469873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152447005739/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-469873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c39 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((29881/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142083/400000) (δ := 6841/1000000000) (ψ := -592023/1000000) 134 78
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t39 : ((47831864751/2000000000000 : ℚ) : ℝ) ≤ stT134 39 := by
  have hc : ((29871/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47831864751/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((29871/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c40 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((20171/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146977/400000) (δ := 3367/500000000) (ψ := -592023/1000000) 134 79
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t40 : ((15938661609/1000000000000 : ℚ) : ℝ) ≤ stT134 40 := by
  have hc : ((20161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15938661609/1000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((20161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c41 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-265037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1149399/2500000) (δ := 3367/500000000) (ψ := -592023/1000000) 134 79
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t41 : ((-206998220603/5000000000000 : ℚ) : ℝ) ≤ stT134 41 := by
  have hc : ((-265087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206998220603/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-265087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c42 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((348273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3037671/10000000) (δ := 847/125000000) (ψ := -592023/1000000) 134 80
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t42 : ((537319580359/10000000000000 : ℚ) : ℝ) ≤ stT134 42 := by
  have hc : ((348223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537319580359/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((348223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c43 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-22439/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2422523/5000000) (δ := 6827/1000000000) (ψ := -592023/1000000) 134 80
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t43 : ((-136895705741/2500000000000 : ℚ) : ℝ) ≤ stT134 43 := by
  have hc : ((-179537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136895705741/2500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-179537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c44 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((301459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1580717/5000000) (δ := 6883/1000000000) (ψ := -592023/1000000) 134 81
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t44 : ((113597736601/2500000000000 : ℚ) : ℝ) ≤ stT134 44 := by
  have hc : ((301409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113597736601/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((301409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c45 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-87539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2183477/5000000) (δ := 6883/1000000000) (ψ := -592023/1000000) 134 81
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t45 : ((-4079147049/156250000000 : ℚ) : ℝ) ≤ stT134 45 := by
  have hc : ((-21891/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4079147049/156250000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-21891/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c46 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-20433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1989039/5000000) (δ := 679/100000000) (ψ := -592023/1000000) 134 82
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t46 : ((-1510027243/500000000000 : ℚ) : ℝ) ≤ stT134 46 := by
  have hc : ((-20483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1510027243/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-20483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c47 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((69133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806633/2500000) (δ := 6813/1000000000) (ψ := -592023/1000000) 134 82
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t47 : ((201645096409/5000000000000 : ℚ) : ℝ) ≤ stT134 47 := by
  have hc : ((138241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201645096409/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((138241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c48 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-282577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2714271/5000000) (δ := 3353/500000000) (ψ := -592023/1000000) 134 83
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t48 : ((-12746904511/156250000000 : ℚ) : ℝ) ≤ stT134 48 := by
  have hc : ((-141301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12746904511/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-141301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c49 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((415037/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147889/1000000) (δ := 3353/500000000) (ψ := -592023/1000000) 134 83
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t49 : ((148218526963/1250000000000 : ℚ) : ℝ) ≤ stT134 49 := by
  have hc : ((103753/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148218526963/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((103753/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c50 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-987679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1492227/2000000) (δ := 1361/200000000) (ψ := -592023/1000000) 134 84
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t50 : ((-698430090003/5000000000000 : ℚ) : ℝ) ≤ stT134 50 := by
  have hc : ((-987729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-698430090003/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-987729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c51 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((945749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6463/78125) (δ := 1361/200000000) (ψ := -592023/1000000) 134 84
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t51 : ((33106084893/250000000000 : ℚ) : ℝ) ≤ stT134 51 := by
  have hc : ((945699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33106084893/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((945699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c52 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-128893/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5677799/10000000) (δ := 3399/500000000) (ψ := -592023/1000000) 134 84
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t52 : ((-178756364153/2000000000000 : ℚ) : ℝ) ≤ stT134 52 := by
  have hc : ((-128903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178756364153/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-128903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c53 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((110961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3649017/10000000) (δ := 839/125000000) (ψ := -592023/1000000) 134 85
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t53 : ((30469580831/2000000000000 : ℚ) : ℝ) ≤ stT134 53 := by
  have hc : ((110911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30469580831/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((110911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c54 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((250893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653209/2500000) (δ := 6891/1000000000) (ψ := -592023/1000000) 134 85
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t54 : ((85346986959/1250000000000 : ℚ) : ℝ) ≤ stT134 54 := by
  have hc : ((62717/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85346986959/1250000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((62717/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c55 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-935077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3474089/5000000) (δ := 6819/1000000000) (ψ := -592023/1000000) 134 86
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t55 : ((-3152313117/25000000000 : ℚ) : ℝ) ≤ stT134 55 := by
  have hc : ((-935127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3152313117/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-935127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c56 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((467099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -911981/10000000) (δ := 53/7812500) (ψ := -592023/1000000) 134 86
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t56 : ((156038447161/1250000000000 : ℚ) : ℝ) ≤ stT134 56 := by
  have hc : ((233537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156038447161/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((233537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c57 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-21123/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1003477/2000000) (δ := 53/7812500) (ψ := -592023/1000000) 134 86
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t57 : ((-55962843783/1000000000000 : ℚ) : ℝ) ≤ stT134 57 := by
  have hc : ((-42251/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55962843783/1000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-42251/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c58 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-366211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194573/400000) (δ := 3363/500000000) (ψ := -592023/1000000) 134 87
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t58 : ((-96184899993/2000000000000 : ℚ) : ℝ) ≤ stT134 58 := by
  have hc : ((-366261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96184899993/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-366261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c59 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((941103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 862299/10000000) (δ := 3363/500000000) (ψ := -592023/1000000) 134 87
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t59 : ((1225146549117/10000000000000 : ℚ) : ℝ) ≤ stT134 59 := by
  have hc : ((941053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1225146549117/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((941053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c60 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-6843/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6492677/10000000) (δ := 6877/1000000000) (ψ := -592023/1000000) 134 87
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t60 : ((-8834795183/80000000000 : ℚ) : ℝ) ≤ stT134 60 := by
  have hc : ((-34217/40000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8834795183/80000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-34217/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c61 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((24861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367797/1000000) (δ := 6833/1000000000) (ψ := -592023/1000000) 134 88
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t61 : ((3976903031/312500000000 : ℚ) : ℝ) ≤ stT134 61 := by
  have hc : ((49697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3976903031/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((49697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c62 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((759847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1769297/10000000) (δ := 677/100000000) (ψ := -592023/1000000) 134 88
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t62 : ((964942949797/10000000000000 : ℚ) : ℝ) ≤ stT134 62 := by
  have hc : ((759797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((964942949797/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((759797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c63 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-191659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7129431/10000000) (δ := 677/100000000) (ψ := -592023/1000000) 134 88
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t63 : ((-120740161529/1000000000000 : ℚ) : ℝ) ≤ stT134 63 := by
  have hc : ((-191669/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120740161529/1000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-191669/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c64 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((24707/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -825713/2500000) (δ := 6863/1000000000) (ψ := -592023/1000000) 134 89
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t64 : ((12351/400000 : ℚ) : ℝ) ≤ stT134 64 := by
  have hc : ((12351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12351/400000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((12351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c65 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((11364/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378211/2000000) (δ := 6863/1000000000) (ψ := -592023/1000000) 134 89
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t65 : ((451018697181/5000000000000 : ℚ) : ℝ) ≤ stT134 65 := by
  have hc : ((363623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((451018697181/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((363623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c66 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-942979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1751417/2500000) (δ := 337/50000000) (ψ := -592023/1000000) 134 89
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t66 : ((-232157708307/2000000000000 : ℚ) : ℝ) ≤ stT134 66 := by
  have hc : ((-943029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232157708307/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-943029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c67 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((26191/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3664599/10000000) (δ := 1351/200000000) (ψ := -592023/1000000) 134 90
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t67 : ((31982116379/2500000000000 : ℚ) : ℝ) ≤ stT134 67 := by
  have hc : ((52357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31982116379/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((52357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c68 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((1389/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64923/500000) (δ := 107/15625000) (ψ := -592023/1000000) 134 90
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t68 : ((21053909097/200000000000 : ℚ) : ℝ) ≤ stT134 68 := by
  have hc : ((34723/40000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21053909097/200000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((34723/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c69 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-393159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3094529/5000000) (δ := 107/15625000) (ψ := -592023/1000000) 134 90
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t69 : ((-14791815533/156250000000 : ℚ) : ℝ) ≤ stT134 69 := by
  have hc : ((-12287/15625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14791815533/156250000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-12287/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c70 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-303801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4698691/10000000) (δ := 1351/200000000) (ψ := -592023/1000000) 134 91
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t70 : ((-363171526879/10000000000000 : ℚ) : ℝ) ≤ stT134 70 := by
  have hc : ((-303851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363171526879/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-303851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c71 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((499887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1063/200000) (δ := 1351/200000000) (ψ := -592023/1000000) 134 91
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t71 : ((296613362111/2500000000000 : ℚ) : ℝ) ≤ stT134 71 := by
  have hc : ((249931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296613362111/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((249931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c72 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-79739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7404/15625) (δ := 107/15625000) (ψ := -592023/1000000) 134 91
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t72 : ((-11748512471/312500000000 : ℚ) : ℝ) ≤ stT134 72 := by
  have hc : ((-159503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11748512471/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-159503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c73 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-824129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6348647/10000000) (δ := 3431/500000000) (ψ := -592023/1000000) 134 92
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t73 : ((-241157247937/2500000000000 : ℚ) : ℝ) ≤ stT134 73 := by
  have hc : ((-824179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241157247937/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-824179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c74 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((150847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1790771/10000000) (δ := 3431/500000000) (ψ := -592023/1000000) 134 92
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t74 : ((43836098103/500000000000 : ℚ) : ℝ) ≤ stT134 74 := by
  have hc : ((150837/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43836098103/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((150837/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c75 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((234611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2705967/10000000) (δ := 6741/1000000000) (ψ := -592023/1000000) 134 92
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t75 : ((1354382271/25000000000 : ℚ) : ℝ) ≤ stT134 75 := by
  have hc : ((117293/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1354382271/25000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((117293/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c76 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-239961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7143109/10000000) (δ := 6741/1000000000) (ψ := -592023/1000000) 134 92
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t76 : ((-550537124813/5000000000000 : ℚ) : ℝ) ≤ stT134 76 := by
  have hc : ((-479947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550537124813/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-479947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c77 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-103299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4185701/10000000) (δ := 3417/500000000) (ψ := -592023/1000000) 134 93
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t77 : ((-58888570247/5000000000000 : ℚ) : ℝ) ≤ stT134 77 := by
  have hc : ((-103349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58888570247/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-103349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c78 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((1997/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68469/5000000) (δ := 3417/500000000) (ψ := -592023/1000000) 134 93
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t78 : ((22610439413/200000000000 : ℚ) : ℝ) ≤ stT134 78 := by
  have hc : ((19969/20000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22610439413/200000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((19969/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c79 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-94923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4404503/10000000) (δ := 3417/500000000) (ψ := -592023/1000000) 134 93
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t79 : ((-834569183/39062500000 : ℚ) : ℝ) ≤ stT134 79 := by
  have hc : ((-23737/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-834569183/39062500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-23737/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c80 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-59601/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3544781/5000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 94
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t80 : ((-266557753161/2500000000000 : ℚ) : ℝ) ≤ stT134 80 := by
  have hc : ((-476833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266557753161/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-476833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c81 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((194519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -366003/1250000) (δ := 1719/250000000) (ψ := -592023/1000000) 134 94
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t81 : ((108052211417/2500000000000 : ℚ) : ℝ) ≤ stT134 81 := by
  have hc : ((97247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108052211417/2500000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((97247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c82 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((890213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1182459/10000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 94
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t82 : ((196604070669/2000000000000 : ℚ) : ℝ) ≤ stT134 82 := by
  have hc : ((890163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196604070669/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((890163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c83 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-502471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655391/1250000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 94
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t83 : ((-551588658003/10000000000000 : ℚ) : ℝ) ≤ stT134 83 := by
  have hc : ((-502521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551588658003/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-502521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c84 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-847009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258113/400000) (δ := 13419/1000000000) (ψ := -592023/1000000) 134 95
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t84 : ((-92421760431/1000000000000 : ℚ) : ℝ) ≤ stT134 84 := by
  have hc : ((-847059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92421760431/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-847059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c85 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((6803/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -622071/2500000) (δ := 53/7812500) (ψ := -592023/1000000) 134 95
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t85 : ((14756419297/250000000000 : ℚ) : ℝ) ≤ stT134 85 := by
  have hc : ((54419/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14756419297/250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((54419/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c86 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((840847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357469/2500000) (δ := 53/7812500) (ψ := -592023/1000000) 134 95
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t86 : ((906654106619/10000000000000 : ℚ) : ℝ) ≤ stT134 86 := by
  have hc : ((840797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((906654106619/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((840797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c87 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-104591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5302777/10000000) (δ := 6819/1000000000) (ψ := -592023/1000000) 134 95
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t87 : ((-112144091913/2000000000000 : ℚ) : ℝ) ≤ stT134 87 := by
  have hc : ((-104601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112144091913/2000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-104601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c88 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-872273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6576571/10000000) (δ := 6891/1000000000) (ψ := -592023/1000000) 134 96
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t88 : ((-232474951823/2500000000000 : ℚ) : ℝ) ≤ stT134 88 := by
  have hc : ((-872323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232474951823/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-872323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c89 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((219417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2791239/10000000) (δ := 839/125000000) (ψ := -592023/1000000) 134 96
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t89 : ((908417429/19531250000 : ℚ) : ℝ) ≤ stT134 89 := by
  have hc : ((6856/15625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((908417429/19531250000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((6856/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c90 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((185679/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 951817/10000000) (δ := 6891/1000000000) (ψ := -592023/1000000) 134 96
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t90 : ((48928051887/500000000000 : ℚ) : ℝ) ≤ stT134 90 := by
  have hc : ((185669/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48928051887/500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((185669/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c91 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-286537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1163379/2500000) (δ := 1689/125000000) (ψ := -592023/1000000) 134 96
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t91 : ((-60084970659/2000000000000 : ℚ) : ℝ) ≤ stT134 91 := by
  have hc : ((-286587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60084970659/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-286587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c92 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-122883/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1478643/2000000) (δ := 3399/500000000) (ψ := -592023/1000000) 134 97
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t92 : ((-512484056161/5000000000000 : ℚ) : ℝ) ≤ stT134 92 := by
  have hc : ((-491557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512484056161/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-491557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c93 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((62131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -942891/2500000) (δ := 1361/200000000) (ψ := -592023/1000000) 134 97
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t93 : ((64374955031/10000000000000 : ℚ) : ℝ) ≤ stT134 93 := by
  have hc : ((62081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64374955031/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((62081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c94 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((199431/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94319/5000000) (δ := 3399/500000000) (ψ := -592023/1000000) 134 97
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t94 : ((205687007241/2000000000000 : ℚ) : ℝ) ≤ stT134 94 := by
  have hc : ((199421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205687007241/2000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((199421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c95 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((113137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 671273/2000000) (δ := 1361/200000000) (ψ := -592023/1000000) 134 97
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t95 : ((7253151471/312500000000 : ℚ) : ℝ) ≤ stT134 95 := by
  have hc : ((14139/62500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7253151471/312500000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((14139/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c96 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-922653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6864251/10000000) (δ := 3399/500000000) (ψ := -592023/1000000) 134 97
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t96 : ((-941730058563/10000000000000 : ℚ) : ℝ) ≤ stT134 96 := by
  have hc : ((-922703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-941730058563/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-922703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c97 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-136603/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214887/400000) (δ := 3449/500000000) (ψ := -592023/1000000) 134 98
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t97 : ((-277424276157/5000000000000 : ℚ) : ℝ) ≤ stT134 97 := by
  have hc : ((-273231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277424276157/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-273231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c98 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((178693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1936247/10000000) (δ := 1341/200000000) (ψ := -592023/1000000) 134 98
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t98 : ((45123616109/625000000000 : ℚ) : ℝ) ≤ stT134 98 := by
  have hc : ((357361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45123616109/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((357361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c99 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((416601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1464807/10000000) (δ := 1341/200000000) (ψ := -592023/1000000) 134 98
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t99 : ((6541785833/78125000000 : ℚ) : ℝ) ≤ stT134 99 := by
  have hc : ((13018/15625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6541785833/78125000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((13018/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c100 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-17701/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4831657/10000000) (δ := 3449/500000000) (ψ := -592023/1000000) 134 98
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t100 : ((-35407/1000000 : ℚ) : ℝ) ≤ stT134 100 := by
  have hc : ((-35407/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35407/1000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-35407/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c101 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-992269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3771461/5000000) (δ := 6791/1000000000) (ψ := -592023/1000000) 134 99
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t101 : ((-493697556561/5000000000000 : ℚ) : ℝ) ≤ stT134 101 := by
  have hc : ((-992319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-493697556561/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-992319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c102 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-12583/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4242401/10000000) (δ := 1703/250000000) (ψ := -592023/1000000) 134 99
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t102 : ((-778998939/62500000000 : ℚ) : ℝ) ≤ stT134 102 := by
  have hc : ((-3147/25000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-778998939/62500000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-3147/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c103 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((185009/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243527/2500000) (δ := 6791/1000000000) (ψ := -592023/1000000) 134 99
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t103 : ((182284879671/2000000000000 : ℚ) : ℝ) ≤ stT134 103 := by
  have hc : ((184999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182284879671/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((184999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c104 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((123529/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2262629/10000000) (δ := 1703/250000000) (ψ := -592023/1000000) 134 99
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t104 : ((6056013051/100000000000 : ℚ) : ℝ) ≤ stT134 104 := by
  have hc : ((123519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6056013051/100000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((123519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c105 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-578239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5468411/10000000) (δ := 6791/1000000000) (ψ := -592023/1000000) 134 99
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t105 : ((-564352813389/10000000000000 : ℚ) : ℝ) ≤ stT134 105 := by
  have hc : ((-578289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564352813389/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-578289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c106 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-59407/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1766047/2500000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 100
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t106 : ((-230816890683/2500000000000 : ℚ) : ℝ) ≤ stT134 106 := by
  have hc : ((-475281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230816890683/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-475281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c107 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((1677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -783721/2000000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 100
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t107 : ((24953873/78125000000 : ℚ) : ℝ) ≤ stT134 107 := by
  have hc : ((413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24953873/78125000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c108 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((189789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -802301/10000000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 100
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t108 : ((730459371/8000000000 : ℚ) : ℝ) ≤ stT134 108 := by
  have hc : ((189779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((730459371/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((189779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c109 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((1221/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114263/500000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 100
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t109 : ((5847048817/100000000000 : ℚ) : ℝ) ≤ stT134 109 := by
  have hc : ((12209/20000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5847048817/100000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((12209/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c110 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-537157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 668081/1250000) (δ := 6719/1000000000) (ψ := -592023/1000000) 134 100
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t110 : ((-512206997841/10000000000000 : ℚ) : ℝ) ≤ stT134 110 := by
  have hc : ((-537207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512206997841/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-537207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c111 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-978249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7331599/10000000) (δ := 847/125000000) (ψ := -592023/1000000) 134 101
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t111 : ((-464280161121/5000000000000 : ℚ) : ℝ) ≤ stT134 111 := by
  have hc : ((-978299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464280161121/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-978299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c112 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-19921/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2163559/5000000) (δ := 847/125000000) (ψ := -592023/1000000) 134 101
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t112 : ((-4707374413/312500000000 : ℚ) : ℝ) ≤ stT134 112 := by
  have hc : ((-79709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4707374413/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-79709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c113 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((214463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1349303/10000000) (δ := 847/125000000) (ψ := -592023/1000000) 134 101
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t113 : ((5043446859/62500000000 : ℚ) : ℝ) ≤ stT134 113 := by
  have hc : ((428901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5043446859/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((428901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c114 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((400779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200281/1250000) (δ := 847/125000000) (ψ := -592023/1000000) 134 101
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t114 : ((37534018509/500000000000 : ℚ) : ℝ) ≤ stT134 114 := by
  have hc : ((200377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37534018509/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((200377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c115 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-238109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2264019/5000000) (δ := 6827/1000000000) (ψ := -592023/1000000) 134 101
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t115 : ((-44416891659/2000000000000 : ℚ) : ℝ) ≤ stT134 115 := by
  have hc : ((-238159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44416891659/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-238159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c116 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-19711/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1857117/2500000) (δ := 6827/1000000000) (ψ := -592023/1000000) 134 101
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t116 : ((-71492729/781250000 : ℚ) : ℝ) ≤ stT134 116 := by
  have hc : ((-616/625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71492729/781250000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-616/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c117 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-557003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5403923/10000000) (δ := 6869/1000000000) (ψ := -592023/1000000) 134 102
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t117 : ((-514996055553/10000000000000 : ℚ) : ℝ) ≤ stT134 117 := by
  have hc : ((-557053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-514996055553/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-557053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c118 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((261199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1276419/5000000) (δ := 3367/500000000) (ψ := -592023/1000000) 134 102
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t118 : ((60107498469/1250000000000 : ℚ) : ℝ) ≤ stT134 118 := by
  have hc : ((130587/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60107498469/1250000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((130587/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c119 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((993993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3427/125000) (δ := 3367/500000000) (ψ := -592023/1000000) 134 102
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t119 : ((455572780107/5000000000000 : ℚ) : ℝ) ≤ stT134 119 := by
  have hc : ((993943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((455572780107/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((993943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c120 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((2083/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153877/500000) (δ := 6869/1000000000) (ψ := -592023/1000000) 134 102
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t120 : ((3041956701/100000000000 : ℚ) : ℝ) ≤ stT134 120 := by
  have hc : ((33323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3041956701/100000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((33323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c121 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-139551/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2928819/5000000) (δ := 6869/1000000000) (ψ := -592023/1000000) 134 102
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t121 : ((-126873649051/2000000000000 : ℚ) : ℝ) ≤ stT134 121 := by
  have hc : ((-139561/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126873649051/2000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-139561/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c122 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-477021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7093107/10000000) (δ := 6841/1000000000) (ψ := -592023/1000000) 134 103
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t122 : ((-107974353117/1250000000000 : ℚ) : ℝ) ≤ stT134 122 := by
  have hc : ((-238523/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107974353117/1250000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-238523/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c123 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-171709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2179201/5000000) (δ := 3381/500000000) (ψ := -592023/1000000) 134 103
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t123 : ((-15486993753/1000000000000 : ℚ) : ℝ) ≤ stT134 123 := by
  have hc : ((-171759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15486993753/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-171759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c124 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((791011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20573/125000) (δ := 3381/500000000) (ψ := -592023/1000000) 134 103
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t124 : ((355151771493/5000000000000 : ℚ) : ℝ) ≤ stT134 124 := by
  have hc : ((790961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355151771493/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((790961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c125 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((913911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1044947/10000000) (δ := 3381/500000000) (ψ := -592023/1000000) 134 103
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t125 : ((817381952647/10000000000000 : ℚ) : ℝ) ≤ stT134 125 := by
  have hc : ((913861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((817381952647/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((913861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c126 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((5311/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1857147/5000000) (δ := 3381/500000000) (ψ := -592023/1000000) 134 103
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t126 : ((3782901281/500000000000 : ℚ) : ℝ) ≤ stT134 126 := by
  have hc : ((42463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3782901281/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((42463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c127 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-165451/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6362503/10000000) (δ := 6841/1000000000) (ψ := -592023/1000000) 134 103
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t127 : ((-146822976577/2000000000000 : ℚ) : ℝ) ≤ stT134 127 := by
  have hc : ((-165461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146822976577/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-165461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c128 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-449263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6717989/10000000) (δ := 1371/200000000) (ψ := -592023/1000000) 134 104
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t128 : ((-12409952331/156250000000 : ℚ) : ℝ) ≤ stT134 128 := by
  have hc : ((-56161/62500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12409952331/156250000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-56161/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c129 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-36759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -513869/1250000) (δ := 1371/200000000) (ψ := -592023/1000000) 134 104
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t129 : ((-2024156849/312500000000 : ℚ) : ℝ) ≤ stT134 129 := by
  have hc : ((-2299/31250 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2024156849/312500000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-2299/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c130 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((409929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -762041/5000000) (δ := 1371/200000000) (ψ := -592023/1000000) 134 104
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t130 : ((11234674451/156250000000 : ℚ) : ℝ) ≤ stT134 130 := by
  have hc : ((25619/31250 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11234674451/156250000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((25619/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c131 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((914229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104299/1000000) (δ := 1687/250000000) (ψ := -592023/1000000) 134 104
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t131 : ((99840231127/1250000000000 : ℚ) : ℝ) ≤ stT134 131 := by
  have hc : ((914179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99840231127/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((914179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c132 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((67089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3590531/10000000) (δ := 1687/250000000) (ψ := -592023/1000000) 134 104
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t132 : ((1824115651/156250000000 : ℚ) : ℝ) ≤ stT134 132 := by
  have hc : ((8383/62500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1824115651/156250000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((8383/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c133 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-384329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6118843/10000000) (δ := 1687/250000000) (ψ := -592023/1000000) 134 104
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t133 : ((-16663859847/250000000000 : ℚ) : ℝ) ≤ stT134 133 := by
  have hc : ((-192177/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16663859847/250000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-192177/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c134 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-238107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7079753/10000000) (δ := 3387/250000000) (ψ := -592023/1000000) 134 105
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t134 : ((-411408108691/5000000000000 : ℚ) : ℝ) ≤ stT134 134 := by
  have hc : ((-476239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411408108691/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-476239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c135 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-261737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1147261/2500000) (δ := 1371/200000000) (ψ := -592023/1000000) 134 105
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t135 : ((-225310384781/10000000000000 : ℚ) : ℝ) ≤ stT134 135 := by
  have hc : ((-261787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225310384781/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-261787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c136 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((66247/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2116711/10000000) (δ := 1687/250000000) (ψ := -592023/1000000) 134 105
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t136 : ((7100248133/125000000000 : ℚ) : ℝ) ≤ stT134 136 := by
  have hc : ((33121/50000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7100248133/125000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((33121/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c137 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((9909/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 337533/10000000) (δ := 1371/200000000) (ψ := -592023/1000000) 134 105
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t137 : ((16930792669/200000000000 : ℚ) : ℝ) ≤ stT134 137 := by
  have hc : ((19817/20000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16930792669/200000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((19817/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c138 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((22253/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2773887/10000000) (δ := 1687/250000000) (ψ := -592023/1000000) 134 105
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t138 : ((4735217907/125000000000 : ℚ) : ℝ) ≤ stT134 138 := by
  have hc : ((44501/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4735217907/125000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((44501/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c139 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-242463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 324543/625000) (δ := 1371/200000000) (ψ := -592023/1000000) 134 105
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t139 : ((-25709456779/625000000000 : ℚ) : ℝ) ≤ stT134 139 := by
  have hc : ((-30311/62500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25709456779/625000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-30311/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c140 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-994603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1518827/2000000) (δ := 1687/250000000) (ψ := -592023/1000000) 134 105
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t140 : ((-168127191243/2000000000000 : ℚ) : ℝ) ≤ stT134 140 := by
  have hc : ((-994653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168127191243/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-994653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c141 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-660139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5729499/10000000) (δ := 6763/1000000000) (ψ := -592023/1000000) 134 106
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t141 : ((-69497435841/1250000000000 : ℚ) : ℝ) ≤ stT134 141 := by
  have hc : ((-660189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69497435841/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-660189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c142 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((224083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3361987/10000000) (δ := 6763/1000000000) (ψ := -592023/1000000) 134 106
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t142 : ((188004236973/10000000000000 : ℚ) : ℝ) ≤ stT134 142 := by
  have hc : ((224033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188004236973/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((224033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c143 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((229831/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011091/10000000) (δ := 6763/1000000000) (ψ := -592023/1000000) 134 106
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t143 : ((192183882077/2500000000000 : ℚ) : ℝ) ≤ stT134 143 := by
  have hc : ((459637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192183882077/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((459637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c144 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((215783/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132339/1000000) (δ := 6763/1000000000) (ψ := -592023/1000000) 134 106
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t144 : ((359617356153/5000000000000 : ℚ) : ℝ) ≤ stT134 144 := by
  have hc : ((431541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((359617356153/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((431541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c145 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((56923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3641757/10000000) (δ := 171/25000000) (ψ := -592023/1000000) 134 106
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t145 : ((11812792923/1250000000000 : ℚ) : ℝ) ≤ stT134 145 := by
  have hc : ((28449/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11812792923/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((28449/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c146 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-722129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5944179/10000000) (δ := 6763/1000000000) (ψ := -592023/1000000) 134 106
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t146 : ((-298839836737/5000000000000 : ℚ) : ℝ) ≤ stT134 146 := by
  have hc : ((-722179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298839836737/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-722179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c147 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-988659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1869277/2500000) (δ := 6733/1000000000) (ψ := -592023/1000000) 134 107
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t147 : ((-815474329983/10000000000000 : ℚ) : ℝ) ≤ stT134 147 := by
  have hc : ((-988709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-815474329983/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-988709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c148 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-61193/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1301477/2500000) (δ := 687/100000000) (ψ := -592023/1000000) 134 107
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t148 : ((-40244382003/1000000000000 : ℚ) : ℝ) ≤ stT134 148 := by
  have hc : ((-244797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40244382003/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-244797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c149 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((38093/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -589997/2000000) (δ := 6733/1000000000) (ψ := -592023/1000000) 134 107
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t149 : ((3900358791/125000000000 : ℚ) : ℝ) ≤ stT134 149 := by
  have hc : ((4761/12500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3900358791/125000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((4761/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c150 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((30001/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -709203/10000000) (δ := 687/100000000) (ψ := -592023/1000000) 134 107
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t150 : ((24494420721/312500000000 : ℚ) : ℝ) ≤ stT134 150 := by
  have hc : ((479991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24494420721/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((479991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c151 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((821537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 758369/5000000) (δ := 687/100000000) (ψ := -592023/1000000) 134 107
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t151 : ((167129065689/2500000000000 : ℚ) : ℝ) ≤ stT134 151 := by
  have hc : ((821487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167129065689/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((821487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c152 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((79523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 931993/2500000) (δ := 6733/1000000000) (ψ := -592023/1000000) 134 107
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t152 : ((64461106611/10000000000000 : ℚ) : ℝ) ≤ stT134 152 := by
  have hc : ((79473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64461106611/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((79473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c153 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-358359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5924701/10000000) (δ := 6733/1000000000) (ψ := -592023/1000000) 134 107
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t153 : ((-18108538747/312500000000 : ℚ) : ℝ) ≤ stT134 153 := by
  have hc : ((-22399/31250 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18108538747/312500000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-22399/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c154 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-497439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3800419/5000000) (δ := 3413/500000000) (ψ := -592023/1000000) 134 108
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t154 : ((-50108491609/625000000000 : ℚ) : ℝ) ≤ stT134 154 := by
  have hc : ((-62183/62500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50108491609/625000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-62183/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c155 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-141619/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108651/200000) (δ := 6777/1000000000) (ψ := -592023/1000000) 134 108
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t155 : ((-11376125343/250000000000 : ℚ) : ℝ) ≤ stT134 155 := by
  have hc : ((-283263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11376125343/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-283263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c156 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((256613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3278199/10000000) (δ := 3413/500000000) (ψ := -592023/1000000) 134 108
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t156 : ((320960313/15625000000 : ℚ) : ℝ) ≤ stT134 156 := by
  have hc : ((256563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320960313/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((256563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c157 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((898241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71101/625000) (δ := 3413/500000000) (ψ := -592023/1000000) 134 108
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t157 : ((358416831213/5000000000000 : ℚ) : ℝ) ≤ stT134 157 := by
  have hc : ((898191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358416831213/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((898191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c158 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((922709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 494683/5000000) (δ := 3413/500000000) (ψ := -592023/1000000) 134 108
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t158 : ((734027826063/10000000000000 : ℚ) : ℝ) ≤ stT134 158 := by
  have hc : ((922659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734027826063/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((922659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c159 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((323681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 775737/2500000) (δ := 3413/500000000) (ψ := -592023/1000000) 134 108
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t159 : ((256655888181/10000000000000 : ℚ) : ℝ) ≤ stT134 159 := by
  have hc : ((323631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256655888181/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((323631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c160 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-244311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81301/156250) (δ := 3413/500000000) (ψ := -592023/1000000) 134 108
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t160 : ((-1207279447/31250000000 : ℚ) : ℝ) ≤ stT134 160 := by
  have hc : ((-15271/31250 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1207279447/31250000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-15271/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c161 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-194941/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3645241/5000000) (δ := 6777/1000000000) (ψ := -592023/1000000) 134 108
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t161 : ((-153643027561/2000000000000 : ℚ) : ℝ) ≤ stT134 161 := by
  have hc : ((-194951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153643027561/2000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-194951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c162 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-205721/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6343161/10000000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 109
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t162 : ((-12931173409/200000000000 : ℚ) : ℝ) ≤ stT134 162 := by
  have hc : ((-411467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12931173409/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-411467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c163 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-14137/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -856321/2000000) (δ := 6719/1000000000) (ψ := -592023/1000000) 134 109
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t163 : ((-5538438531/500000000000 : ℚ) : ℝ) ≤ stT134 163 := by
  have hc : ((-7071/50000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5538438531/500000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-7071/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c164 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((627023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1116339/5000000) (δ := 6719/1000000000) (ψ := -592023/1000000) 134 109
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t164 : ((122395788141/2500000000000 : ℚ) : ℝ) ≤ stT134 164 := by
  have hc : ((626973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122395788141/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((626973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c165 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((498461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196213/10000000) (δ := 6719/1000000000) (ψ := -592023/1000000) 134 109
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t165 : ((48503928641/625000000000 : ℚ) : ℝ) ≤ stT134 165 := by
  have hc : ((124609/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48503928641/625000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((124609/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c166 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((148877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 913979/5000000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 109
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t166 : ((2310862441/40000000000 : ℚ) : ℝ) ≤ stT134 166 := by
  have hc : ((148867/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2310862441/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((148867/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c167 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((34789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3840001/10000000) (δ := 6719/1000000000) (ψ := -592023/1000000) 134 109
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t167 : ((26881837197/10000000000000 : ℚ) : ℝ) ≤ stT134 167 := by
  have hc : ((34739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26881837197/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((34739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c168 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-17317/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1167997/2000000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 109
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t168 : ((-53445297141/1000000000000 : ℚ) : ℝ) ≤ stT134 168 := by
  have hc : ((-69273/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53445297141/1000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-69273/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c169 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-999947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7828143/10000000) (δ := 1721/250000000) (ψ := -592023/1000000) 134 109
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t169 : ((-769228692307/10000000000000 : ℚ) : ℝ) ≤ stT134 169 := by
  have hc : ((-999997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-769228692307/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-999997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c170 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-177689/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5903421/10000000) (δ := 6791/1000000000) (ψ := -592023/1000000) 134 110
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t170 : ((-54516332379/1000000000000 : ℚ) : ℝ) ≤ stT134 170 := by
  have hc : ((-355403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54516332379/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-355403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c171 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-4649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3938613/10000000) (δ := 1703/250000000) (ψ := -592023/1000000) 134 110
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t171 : ((-44917741/125000000000 : ℚ) : ℝ) ≤ stT134 171 := by
  have hc : ((-4699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44917741/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-4699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c172 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((175231/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1985261/10000000) (δ := 6791/1000000000) (ψ := -592023/1000000) 134 110
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t172 : ((66801352251/1250000000000 : ℚ) : ℝ) ≤ stT134 172 := by
  have hc : ((350437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66801352251/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((350437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c173 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((19997/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43233/10000000) (δ := 1703/250000000) (ψ := -592023/1000000) 134 110
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t173 : ((760132943/10000000000 : ℚ) : ℝ) ≤ stT134 173 := by
  have hc : ((4999/5000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760132943/10000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((4999/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c174 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((364121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1887607/10000000) (δ := 6791/1000000000) (ψ := -592023/1000000) 134 110
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t174 : ((2156409761/39062500000 : ℚ) : ℝ) ≤ stT134 174 := by
  have hc : ((11378/15625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2156409761/39062500000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((11378/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c175 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((23911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3807391/10000000) (δ := 1703/250000000) (ψ := -592023/1000000) 134 110
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t175 : ((1128506013/312500000000 : ℚ) : ℝ) ≤ stT134 175 := by
  have hc : ((11943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1128506013/312500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((11943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c176 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-32807/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5716221/10000000) (δ := 1703/250000000) (ψ := -592023/1000000) 134 110
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t176 : ((-49462224201/1000000000000 : ℚ) : ℝ) ≤ stT134 176 := by
  have hc : ((-65619/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49462224201/1000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-65619/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c177 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-497703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 951783/1250000) (δ := 1703/250000000) (ψ := -592023/1000000) 134 110
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t177 : ((-5845558719/78125000000 : ℚ) : ℝ) ≤ stT134 177 := by
  have hc : ((-15554/15625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5845558719/78125000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-15554/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c178 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-790579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -775797/1250000) (δ := 1341/200000000) (ψ := -592023/1000000) 134 111
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t178 : ((-148150433907/2500000000000 : ℚ) : ℝ) ≤ stT134 178 := by
  have hc : ((-790629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148150433907/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-790629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c179 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-3207/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -865921/2000000) (δ := 3449/500000000) (ψ := -592023/1000000) 134 111
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t179 : ((-74930459/6250000000 : ℚ) : ℝ) ≤ stT134 179 := by
  have hc : ((-401/2500 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74930459/6250000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-401/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c180 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((55259/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61583/250000) (δ := 3449/500000000) (ψ := -592023/1000000) 134 111
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t180 : ((4118384517/100000000000 : ℚ) : ℝ) ≤ stT134 180 := by
  have hc : ((27627/50000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4118384517/100000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((27627/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c181 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((194127/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -607353/10000000) (δ := 3449/500000000) (ψ := -592023/1000000) 134 111
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t181 : ((72143000699/1000000000000 : ℚ) : ℝ) ≤ stT134 181 := by
  have hc : ((194117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72143000699/1000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((194117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c182 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((175961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1238363/10000000) (δ := 3449/500000000) (ψ := -592023/1000000) 134 111
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t182 : ((130423502799/2000000000000 : ℚ) : ℝ) ≤ stT134 182 := by
  have hc : ((175951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130423502799/2000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((175951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c183 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((334617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 614799/2000000) (δ := 1341/200000000) (ψ := -592023/1000000) 134 111
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t183 : ((247318952307/10000000000000 : ℚ) : ℝ) ≤ stT134 183 := by
  have hc : ((334567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247318952307/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((334567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c184 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-94827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4899611/10000000) (δ := 1341/200000000) (ψ := -592023/1000000) 134 111
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t184 : ((-13983325559/500000000000 : ℚ) : ℝ) ≤ stT134 184 := by
  have hc : ((-189679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13983325559/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-189679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c185 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-898061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1343069/2000000) (δ := 3449/500000000) (ψ := -592023/1000000) 134 111
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t185 : ((-132060935773/2000000000000 : ℚ) : ℝ) ≤ stT134 185 := by
  have hc : ((-898111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132060935773/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-898111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c186 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-96459/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7186701/10000000) (δ := 6797/1000000000) (ψ := -592023/1000000) 134 112
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t186 : ((-1105169961/15625000000 : ℚ) : ℝ) ≤ stT134 186 := by
  have hc : ((-6029/6250 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1105169961/15625000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-6029/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c187 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-552513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5390431/10000000) (δ := 6797/1000000000) (ψ := -592023/1000000) 134 112
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t187 : ((-404074402699/10000000000000 : ℚ) : ℝ) ≤ stT134 187 := by
  have hc : ((-552563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404074402699/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-552563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c188 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((64463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144151/400000) (δ := 3403/500000000) (ψ := -592023/1000000) 134 112
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t188 : ((5874522489/625000000000 : ℚ) : ℝ) ≤ stT134 188 := by
  have hc : ((32219/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5874522489/625000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((32219/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c189 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((186189/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1826567/10000000) (δ := 6797/1000000000) (ψ := -592023/1000000) 134 112
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t189 : ((8463956043/156250000000 : ℚ) : ℝ) ≤ stT134 189 := by
  have hc : ((372353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8463956043/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((372353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c190 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((249931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14693/2500000) (δ := 6797/1000000000) (ψ := -592023/1000000) 134 112
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t190 : ((90654936853/1250000000000 : ℚ) : ℝ) ≤ stT134 190 := by
  have hc : ((499837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90654936853/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((499837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c191 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((777629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1699777/10000000) (δ := 6797/1000000000) (ψ := -592023/1000000) 134 112
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t191 : ((281317973673/5000000000000 : ℚ) : ℝ) ≤ stT134 191 := by
  have hc : ((777579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281317973673/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((777579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c192 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((189989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1724557/5000000) (δ := 3403/500000000) (ψ := -592023/1000000) 134 112
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t192 : ((137076507093/10000000000000 : ℚ) : ℝ) ≤ stT134 192 := by
  have hc : ((189939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137076507093/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((189939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c193 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-241883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1297343/2500000) (δ := 3403/500000000) (ψ := -592023/1000000) 134 112
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t193 : ((-5441539029/156250000000 : ℚ) : ℝ) ≤ stT134 193 := by
  have hc : ((-60477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5441539029/156250000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-60477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c194 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-931117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1730163/2500000) (δ := 3403/500000000) (ψ := -592023/1000000) 134 112
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t194 : ((-668539728153/10000000000000 : ℚ) : ℝ) ≤ stT134 194 := by
  have hc : ((-931167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-668539728153/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-931167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c195 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-475303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7064943/10000000) (δ := 689/100000000) (ψ := -592023/1000000) 134 113
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t195 : ((-1063717221/15625000000 : ℚ) : ℝ) ≤ stT134 195 := by
  have hc : ((-14854/15625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1063717221/15625000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-14854/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c196 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-134857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -668923/1250000) (δ := 6713/1000000000) (ψ := -592023/1000000) 134 113
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t196 : ((-96335395677/2500000000000 : ℚ) : ℝ) ≤ stT134 196 := by
  have hc : ((-269739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96335395677/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-269739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c197 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((111947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -455817/1250000) (δ := 689/100000000) (ψ := -592023/1000000) 134 113
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t197 : ((7972325559/1000000000000 : ℚ) : ℝ) ≤ stT134 197 := by
  have hc : ((111897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7972325559/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((111897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c198 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((710821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195033/1000000) (δ := 6713/1000000000) (ψ := -592023/1000000) 134 113
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t198 : ((505122915799/10000000000000 : ℚ) : ℝ) ≤ stT134 198 := by
  have hc : ((710771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((505122915799/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((710771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c199 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((497243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262667/10000000) (δ := 6713/1000000000) (ψ := -592023/1000000) 134 113
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t199 : ((176234196529/2500000000000 : ℚ) : ℝ) ≤ stT134 199 := by
  have hc : ((248609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176234196529/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((248609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c200 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((843727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35413/250000) (δ := 689/100000000) (ψ := -592023/1000000) 134 113
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t200 : ((298284534381/5000000000000 : ℚ) : ℝ) ≤ stT134 200 := by
  have hc : ((843677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298284534381/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((843677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c201 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((82393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543683/5000000) (δ := 689/100000000) (ψ := -592023/1000000) 134 113
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t201 : ((23242669509/1000000000000 : ℚ) : ℝ) ≤ stT134 201 := by
  have hc : ((164761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23242669509/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((164761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c202 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-323241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4749871/10000000) (δ := 6713/1000000000) (ψ := -592023/1000000) 134 113
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t202 : ((-113733450509/5000000000000 : ℚ) : ℝ) ≤ stT134 202 := by
  have hc : ((-323291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113733450509/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-323291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c203 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-836511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6404201/10000000) (δ := 689/100000000) (ψ := -592023/1000000) 134 113
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t203 : ((-587151213143/10000000000000 : ℚ) : ℝ) ≤ stT134 203 := by
  have hc : ((-836561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587151213143/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-836561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c204 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-199383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1914393/2500000) (δ := 6783/1000000000) (ψ := -592023/1000000) 134 114
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t204 : ((-139603214413/2000000000000 : ℚ) : ℝ) ≤ stT134 204 := by
  have hc : ((-199393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139603214413/2000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-199393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c205 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-742619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3009711/5000000) (δ := 6783/1000000000) (ψ := -592023/1000000) 134 114
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t205 : ((-518703052339/10000000000000 : ℚ) : ℝ) ≤ stT134 205 := by
  have hc : ((-742669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518703052339/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-742669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c206 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-3677/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -877849/2000000) (δ := 6783/1000000000) (ψ := -592023/1000000) 134 114
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t206 : ((-640646913/50000000000 : ℚ) : ℝ) ≤ stT134 206 := by
  have hc : ((-1839/10000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640646913/50000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-1839/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c207 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((89507/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1383487/5000000) (δ := 6783/1000000000) (ψ := -592023/1000000) 134 114
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t207 : ((7775588857/250000000000 : ℚ) : ℝ) ≤ stT134 207 := by
  have hc : ((89497/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7775588857/250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((89497/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c208 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((895607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288127/2500000) (δ := 341/50000000) (ψ := -592023/1000000) 134 114
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t208 : ((4967654679/80000000000 : ℚ) : ℝ) ≤ stT134 208 := by
  have hc : ((895557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4967654679/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((895557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c209 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((49177/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 454219/10000000) (δ := 341/50000000) (ψ := -592023/1000000) 134 114
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t209 : ((34014690093/500000000000 : ℚ) : ℝ) ≤ stT134 209 := by
  have hc : ((98349/100000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34014690093/500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((98349/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c210 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((681263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1026637/5000000) (δ := 6783/1000000000) (ψ := -592023/1000000) 134 114
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t210 : ((94016249769/2000000000000 : ℚ) : ℝ) ≤ stT134 210 := by
  have hc : ((681213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94016249769/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((681213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c211 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((112667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145789/400000) (δ := 6783/1000000000) (ψ := -592023/1000000) 134 114
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t211 : ((19382174019/2500000000000 : ℚ) : ℝ) ≤ stT134 211 := by
  have hc : ((112617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19382174019/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((112617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c212 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-124363/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5228639/10000000) (δ := 341/50000000) (ψ := -592023/1000000) 134 114
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t212 : ((-170842933053/5000000000000 : ℚ) : ℝ) ≤ stT134 212 := by
  have hc : ((-248751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170842933053/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-248751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c213 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-456637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1361023/2000000) (δ := 6783/1000000000) (ψ := -592023/1000000) 134 114
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t213 : ((-156449889559/2500000000000 : ℚ) : ℝ) ≤ stT134 213 := by
  have hc : ((-228331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156449889559/2500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-228331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c214 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-489213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3666871/5000000) (δ := 1719/250000000) (ψ := -592023/1000000) 134 115
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t214 : ((-83609061867/1250000000000 : ℚ) : ℝ) ≤ stT134 214 := by
  have hc : ((-244619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83609061867/1250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-244619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c215 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-168201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1442993/2500000) (δ := 1719/250000000) (ψ := -592023/1000000) 134 115
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t215 : ((-45888306373/1000000000000 : ℚ) : ℝ) ≤ stT134 215 := by
  have hc : ((-336427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45888306373/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-336427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c216 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-57959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108719/5000000) (δ := 1719/250000000) (ψ := -592023/1000000) 134 115
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t216 : ((-154113771/19531250000 : ℚ) : ℝ) ≤ stT134 216 := by
  have hc : ((-1812/15625 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154113771/19531250000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-1812/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c217 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((481841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1335053/5000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 115
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t217 : ((81765232401/2500000000000 : ℚ) : ℝ) ≤ stT134 217 := by
  have hc : ((481791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81765232401/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((481791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c218 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((899597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1129877/10000000) (δ := 1719/250000000) (ψ := -592023/1000000) 134 115
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t218 : ((121849937979/2000000000000 : ℚ) : ℝ) ≤ stT134 218 := by
  have hc : ((899547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121849937979/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((899547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c219 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((197403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 201659/5000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 115
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t219 : ((133385753641/2000000000000 : ℚ) : ℝ) ≤ stT134 219 := by
  have hc : ((197393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133385753641/2000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((197393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c220 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((716653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1929511/10000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 115
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t220 : ((483133025997/10000000000000 : ℚ) : ℝ) ≤ stT134 220 := by
  have hc : ((716603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((483133025997/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((716603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c221 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((190111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3448803/10000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 115
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t221 : ((3995272281/312500000000 : ℚ) : ℝ) ≤ stT134 221 := by
  have hc : ((190061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3995272281/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((190061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c222 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-401983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2480597/5000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 115
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t222 : ((-269827262181/10000000000000 : ℚ) : ℝ) ≤ stT134 222 := by
  have hc : ((-402033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269827262181/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-402033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c223 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-849971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3233409/5000000) (δ := 6727/1000000000) (ψ := -592023/1000000) 134 115
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t223 : ((-11384331253/200000000000 : ℚ) : ℝ) ≤ stT134 223 := by
  have hc : ((-850021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11384331253/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-850021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c224 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-499501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1548451/2000000) (δ := 6769/1000000000) (ψ := -592023/1000000) 134 116
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t224 : ((-83440073751/1250000000000 : ℚ) : ℝ) ≤ stT134 224 := by
  have hc : ((-249763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83440073751/1250000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-249763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c225 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-801151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6250031/10000000) (δ := 6769/1000000000) (ψ := -592023/1000000) 134 116
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t225 : ((-534134267067/10000000000000 : ℚ) : ℝ) ≤ stT134 225 := by
  have hc : ((-801201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534134267067/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-801201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c226 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-82189/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4764457/10000000) (δ := 13569/1000000000) (ψ := -592023/1000000) 134 116
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t226 : ((-109359395973/5000000000000 : ℚ) : ℝ) ≤ stT134 226 := by
  have hc : ((-164403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109359395973/5000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-164403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c227 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((253823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -657083/2000000) (δ := 6769/1000000000) (ψ := -592023/1000000) 134 116
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t227 : ((168434976879/10000000000000 : ℚ) : ℝ) ≤ stT134 227 := by
  have hc : ((253773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168434976879/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((253773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c228 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((187099/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1812889/10000000) (δ := 6769/1000000000) (ψ := -592023/1000000) 134 116
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t228 : ((123901028009/2500000000000 : ℚ) : ℝ) ≤ stT134 228 := by
  have hc : ((374173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123901028009/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((374173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c229 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((495197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69359/2000000) (δ := 6769/1000000000) (ψ := -592023/1000000) 134 116
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t229 : ((40902321337/625000000000 : ℚ) : ℝ) ≤ stT134 229 := by
  have hc : ((123793/125000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40902321337/625000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((123793/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c230 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((451271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1112901/10000000) (δ := 3417/500000000) (ψ := -592023/1000000) 134 116
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t230 : ((7438564687/125000000000 : ℚ) : ℝ) ≤ stT134 230 := by
  have hc : ((225623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7438564687/125000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((225623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c231 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((517811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 513253/2000000) (δ := 3417/500000000) (ψ := -592023/1000000) 134 116
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t231 : ((340661367711/10000000000000 : ℚ) : ℝ) ≤ stT134 231 := by
  have hc : ((517761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340661367711/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((517761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c232 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-34529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4013331/10000000) (δ := 3417/500000000) (ψ := -592023/1000000) 134 116
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t232 : ((-22702254607/10000000000000 : ℚ) : ℝ) ≤ stT134 232 := by
  have hc : ((-34579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22702254607/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-34579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c233 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-573591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5454199/10000000) (δ := 6769/1000000000) (ψ := -592023/1000000) 134 116
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t233 : ((-187902419601/5000000000000 : ℚ) : ℝ) ≤ stT134 233 := by
  have hc : ((-573641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187902419601/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-573641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c234 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-926411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 861113/1250000) (δ := 3417/500000000) (ψ := -592023/1000000) 134 116
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t234 : ((-605647011381/10000000000000 : ℚ) : ℝ) ≤ stT134 234 := by
  have hc : ((-926461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-605647011381/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-926461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c235 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-982863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3695243/5000000) (δ := 6861/1000000000) (ψ := -592023/1000000) 134 117
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t235 : ((-641182654377/10000000000000 : ℚ) : ℝ) ≤ stT134 235 := by
  have hc : ((-982913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-641182654377/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-982913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c236 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-728681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238719/400000) (δ := 3371/500000000) (ψ := -592023/1000000) 134 117
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t236 : ((-94872760159/2000000000000 : ℚ) : ℝ) ≤ stT134 236 := by
  have hc : ((-728731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94872760159/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-728731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c237 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-61803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -910299/2000000) (δ := 6861/1000000000) (ψ := -592023/1000000) 134 117
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t237 : ((-8030698867/500000000000 : ℚ) : ℝ) ≤ stT134 237 := by
  have hc : ((-123631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8030698867/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-123631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c238 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((309251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3140977/10000000) (δ := 3371/500000000) (ψ := -592023/1000000) 134 117
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t238 : ((200425015803/10000000000000 : ℚ) : ℝ) ≤ stT134 238 := by
  have hc : ((309201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200425015803/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((309201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c239 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((768347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434089/2500000) (δ := 6861/1000000000) (ψ := -592023/1000000) 134 117
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t239 : ((248484920631/5000000000000 : ℚ) : ℝ) ≤ stT134 239 := by
  have hc : ((768297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248484920631/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((768297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c240 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((61931/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337597/10000000) (δ := 6861/1000000000) (ψ := -592023/1000000) 134 117
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t240 : ((319794060231/5000000000000 : ℚ) : ℝ) ≤ stT134 240 := by
  have hc : ((495423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319794060231/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((495423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c241 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((912217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1055333/10000000) (δ := 6861/1000000000) (ψ := -592023/1000000) 134 117
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t241 : ((146894461513/2500000000000 : ℚ) : ℝ) ≤ stT134 241 := by
  have hc : ((912167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146894461513/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((912167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c242 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((559511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2442501/10000000) (δ := 6861/1000000000) (ψ := -592023/1000000) 134 117
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t242 : ((44954369733/1250000000000 : ℚ) : ℝ) ≤ stT134 242 := by
  have hc : ((559461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44954369733/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((559461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c243 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((5151/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3823941/10000000) (δ := 3371/500000000) (ψ := -592023/1000000) 134 117
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t243 : ((26402857/10000000000 : ℚ) : ℝ) ≤ stT134 243 := by
  have hc : ((20579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26402857/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((20579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c244 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-60923/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5199719/10000000) (δ := 3371/500000000) (ψ := -592023/1000000) 134 117
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t244 : ((-31204793529/1000000000000 : ℚ) : ℝ) ≤ stT134 244 := by
  have hc : ((-243717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31204793529/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-243717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c245 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-217739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1642463/2500000) (δ := 13461/1000000000) (ψ := -592023/1000000) 134 117
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t245 : ((-278232850131/5000000000000 : ℚ) : ℝ) ≤ stT134 245 := by
  have hc : ((-435503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278232850131/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-435503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c246 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-499741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7773539/10000000) (δ := 3377/500000000) (ψ := -592023/1000000) 134 118
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t246 : ((-159319653491/2500000000000 : ℚ) : ℝ) ≤ stT134 246 := by
  have hc : ((-249883/250000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159319653491/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-249883/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c247 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-838763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6414511/10000000) (δ := 3377/500000000) (ψ := -592023/1000000) 134 118
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t247 : ((-106744825941/2000000000000 : ℚ) : ℝ) ≤ stT134 247 := by
  have hc : ((-838813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106744825941/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-838813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c248 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-438199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5060977/10000000) (δ := 3377/500000000) (ψ := -592023/1000000) 134 118
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t248 : ((-278288553249/10000000000000 : ℚ) : ℝ) ≤ stT134 248 := by
  have hc : ((-438249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278288553249/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-438249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c249 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((8553/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3712903/10000000) (δ := 6849/1000000000) (ψ := -592023/1000000) 134 118
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t249 : ((338567047/62500000000 : ℚ) : ℝ) ≤ stT134 249 := by
  have hc : ((2137/25000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338567047/62500000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((2137/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_c250 :
    |Real.cos (((134 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((583247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237019/1000000) (δ := 3377/500000000) (ψ := -592023/1000000) 134 118
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st134_t250 : ((73769171727/2000000000000 : ℚ) : ℝ) ≤ stT134 250 := by
  have hc : ((583197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((134 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st134_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73769171727/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((583197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st134_p1 : ((829763/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT134 (i+1) := by
  rw [Finset.sum_range_one]
  exact st134_t1

theorem st134_p2 : ((3338438507987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT134 (i+1))
      = (∑ i ∈ Finset.range 1, stT134 (i+1)) + stT134 2 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 1
    simpa using h
  have hprev := st134_p1
  have hstep := st134_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p3 : ((1911459506507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT134 (i+1))
      = (∑ i ∈ Finset.range 2, stT134 (i+1)) + stT134 3 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 2
    simpa using h
  have hprev := st134_p2
  have hstep := st134_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p4 : ((2475193743469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT134 (i+1))
      = (∑ i ∈ Finset.range 3, stT134 (i+1)) + stT134 4 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 3
    simpa using h
  have hprev := st134_p3
  have hstep := st134_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p5 : ((527053039489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT134 (i+1))
      = (∑ i ∈ Finset.range 4, stT134 (i+1)) + stT134 5 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 4
    simpa using h
  have hprev := st134_p4
  have hstep := st134_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p6 : ((-184384942989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT134 (i+1))
      = (∑ i ∈ Finset.range 5, stT134 (i+1)) + stT134 6 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 5
    simpa using h
  have hprev := st134_p5
  have hstep := st134_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p7 : ((-1752922499409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT134 (i+1))
      = (∑ i ∈ Finset.range 6, stT134 (i+1)) + stT134 7 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 6
    simpa using h
  have hprev := st134_p6
  have hstep := st134_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p8 : ((-3404603776053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT134 (i+1))
      = (∑ i ∈ Finset.range 7, stT134 (i+1)) + stT134 8 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 7
    simpa using h
  have hprev := st134_p7
  have hstep := st134_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p9 : ((-3614844538209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT134 (i+1))
      = (∑ i ∈ Finset.range 8, stT134 (i+1)) + stT134 9 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 8
    simpa using h
  have hprev := st134_p8
  have hstep := st134_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p10 : ((-1327485069953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT134 (i+1))
      = (∑ i ∈ Finset.range 9, stT134 (i+1)) + stT134 10 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 9
    simpa using h
  have hprev := st134_p9
  have hstep := st134_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p11 : ((-468866418571/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT134 (i+1))
      = (∑ i ∈ Finset.range 10, stT134 (i+1)) + stT134 11 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 10
    simpa using h
  have hprev := st134_p10
  have hstep := st134_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p12 : ((25068865933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT134 (i+1))
      = (∑ i ∈ Finset.range 11, stT134 (i+1)) + stT134 12 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 11
    simpa using h
  have hprev := st134_p11
  have hstep := st134_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p13 : ((111932166029/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT134 (i+1))
      = (∑ i ∈ Finset.range 12, stT134 (i+1)) + stT134 13 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 12
    simpa using h
  have hprev := st134_p12
  have hstep := st134_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p14 : ((-1015426222799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT134 (i+1))
      = (∑ i ∈ Finset.range 13, stT134 (i+1)) + stT134 14 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 13
    simpa using h
  have hprev := st134_p13
  have hstep := st134_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p15 : ((477949160617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT134 (i+1))
      = (∑ i ∈ Finset.range 14, stT134 (i+1)) + stT134 15 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 14
    simpa using h
  have hprev := st134_p14
  have hstep := st134_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p16 : ((875661660617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT134 (i+1))
      = (∑ i ∈ Finset.range 15, stT134 (i+1)) + stT134 16 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 15
    simpa using h
  have hprev := st134_p15
  have hstep := st134_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p17 : ((-383796107113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT134 (i+1))
      = (∑ i ∈ Finset.range 16, stT134 (i+1)) + stT134 17 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 16
    simpa using h
  have hprev := st134_p16
  have hstep := st134_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p18 : ((-1735067049921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT134 (i+1))
      = (∑ i ∈ Finset.range 17, stT134 (i+1)) + stT134 18 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 17
    simpa using h
  have hprev := st134_p17
  have hstep := st134_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p19 : ((14284218993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT134 (i+1))
      = (∑ i ∈ Finset.range 18, stT134 (i+1)) + stT134 19 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 18
    simpa using h
  have hprev := st134_p18
  have hstep := st134_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p20 : ((1126253505289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT134 (i+1))
      = (∑ i ∈ Finset.range 19, stT134 (i+1)) + stT134 20 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 19
    simpa using h
  have hprev := st134_p19
  have hstep := st134_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p21 : ((1102437315643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT134 (i+1))
      = (∑ i ∈ Finset.range 20, stT134 (i+1)) + stT134 21 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 20
    simpa using h
  have hprev := st134_p20
  have hstep := st134_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p22 : ((6530680486207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT134 (i+1))
      = (∑ i ∈ Finset.range 21, stT134 (i+1)) + stT134 22 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 21
    simpa using h
  have hprev := st134_p21
  have hstep := st134_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p23 : ((8563087024159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT134 (i+1))
      = (∑ i ∈ Finset.range 22, stT134 (i+1)) + stT134 23 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 22
    simpa using h
  have hprev := st134_p22
  have hstep := st134_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p24 : ((9977258788959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT134 (i+1))
      = (∑ i ∈ Finset.range 23, stT134 (i+1)) + stT134 24 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 23
    simpa using h
  have hprev := st134_p23
  have hstep := st134_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p25 : ((2470497185331/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT134 (i+1))
      = (∑ i ∈ Finset.range 24, stT134 (i+1)) + stT134 25 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 24
    simpa using h
  have hprev := st134_p24
  have hstep := st134_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p26 : ((50979201007/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT134 (i+1))
      = (∑ i ∈ Finset.range 25, stT134 (i+1)) + stT134 26 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 25
    simpa using h
  have hprev := st134_p25
  have hstep := st134_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p27 : ((1344601103733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT134 (i+1))
      = (∑ i ∈ Finset.range 26, stT134 (i+1)) + stT134 27 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 26
    simpa using h
  have hprev := st134_p26
  have hstep := st134_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p28 : ((7741955964981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT134 (i+1))
      = (∑ i ∈ Finset.range 27, stT134 (i+1)) + stT134 28 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 27
    simpa using h
  have hprev := st134_p27
  have hstep := st134_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p29 : ((2323866533051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT134 (i+1))
      = (∑ i ∈ Finset.range 28, stT134 (i+1)) + stT134 29 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 28
    simpa using h
  have hprev := st134_p28
  have hstep := st134_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p30 : ((1006482746113/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT134 (i+1))
      = (∑ i ∈ Finset.range 29, stT134 (i+1)) + stT134 30 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 29
    simpa using h
  have hprev := st134_p29
  have hstep := st134_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p31 : ((1796496981903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT134 (i+1))
      = (∑ i ∈ Finset.range 30, stT134 (i+1)) + stT134 31 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 30
    simpa using h
  have hprev := st134_p30
  have hstep := st134_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p32 : ((4475940931709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT134 (i+1))
      = (∑ i ∈ Finset.range 31, stT134 (i+1)) + stT134 32 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 31
    simpa using h
  have hprev := st134_p31
  have hstep := st134_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p33 : ((2012683458457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT134 (i+1))
      = (∑ i ∈ Finset.range 32, stT134 (i+1)) + stT134 33 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 32
    simpa using h
  have hprev := st134_p32
  have hstep := st134_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p34 : ((3759949681103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT134 (i+1))
      = (∑ i ∈ Finset.range 33, stT134 (i+1)) + stT134 34 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 33
    simpa using h
  have hprev := st134_p33
  have hstep := st134_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p35 : ((4496094873029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT134 (i+1))
      = (∑ i ∈ Finset.range 34, stT134 (i+1)) + stT134 35 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 34
    simpa using h
  have hprev := st134_p34
  have hstep := st134_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p36 : ((3668701374217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT134 (i+1))
      = (∑ i ∈ Finset.range 35, stT134 (i+1)) + stT134 36 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 35
    simpa using h
  have hprev := st134_p35
  have hstep := st134_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p37 : ((1729262453293/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT134 (i+1))
      = (∑ i ∈ Finset.range 36, stT134 (i+1)) + stT134 37 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 36
    simpa using h
  have hprev := st134_p36
  have hstep := st134_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p38 : ((788407723777/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT134 (i+1))
      = (∑ i ∈ Finset.range 37, stT134 (i+1)) + stT134 38 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 37
    simpa using h
  have hprev := st134_p37
  have hstep := st134_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p39 : ((324929462461/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT134 (i+1))
      = (∑ i ∈ Finset.range 38, stT134 (i+1)) + stT134 39 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 38
    simpa using h
  have hprev := st134_p38
  have hstep := st134_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p40 : ((1656524635523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT134 (i+1))
      = (∑ i ∈ Finset.range 39, stT134 (i+1)) + stT134 40 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 39
    simpa using h
  have hprev := st134_p39
  have hstep := st134_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p41 : ((7868626736409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT134 (i+1))
      = (∑ i ∈ Finset.range 40, stT134 (i+1)) + stT134 41 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 40
    simpa using h
  have hprev := st134_p40
  have hstep := st134_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p42 : ((262685822399/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT134 (i+1))
      = (∑ i ∈ Finset.range 41, stT134 (i+1)) + stT134 42 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 41
    simpa using h
  have hprev := st134_p41
  have hstep := st134_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p43 : ((1964590873451/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT134 (i+1))
      = (∑ i ∈ Finset.range 42, stT134 (i+1)) + stT134 43 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 42
    simpa using h
  have hprev := st134_p42
  have hstep := st134_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p44 : ((519547152513/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT134 (i+1))
      = (∑ i ∈ Finset.range 43, stT134 (i+1)) + stT134 44 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 43
    simpa using h
  have hprev := st134_p43
  have hstep := st134_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p45 : ((503230564317/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT134 (i+1))
      = (∑ i ∈ Finset.range 44, stT134 (i+1)) + stT134 45 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 44
    simpa using h
  have hprev := st134_p44
  have hstep := st134_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p46 : ((2005372121053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT134 (i+1))
      = (∑ i ∈ Finset.range 45, stT134 (i+1)) + stT134 46 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 45
    simpa using h
  have hprev := st134_p45
  have hstep := st134_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p47 : ((842477867703/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT134 (i+1))
      = (∑ i ∈ Finset.range 46, stT134 (i+1)) + stT134 47 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 46
    simpa using h
  have hprev := st134_p46
  have hstep := st134_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p48 : ((3804488394163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT134 (i+1))
      = (∑ i ∈ Finset.range 47, stT134 (i+1)) + stT134 48 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 47
    simpa using h
  have hprev := st134_p47
  have hstep := st134_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p49 : ((879472500403/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT134 (i+1))
      = (∑ i ∈ Finset.range 48, stT134 (i+1)) + stT134 49 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 48
    simpa using h
  have hprev := st134_p48
  have hstep := st134_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p50 : ((924733103003/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT134 (i+1))
      = (∑ i ∈ Finset.range 49, stT134 (i+1)) + stT134 50 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 49
    simpa using h
  have hprev := st134_p49
  have hstep := st134_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p51 : ((272565881867/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT134 (i+1))
      = (∑ i ∈ Finset.range 50, stT134 (i+1)) + stT134 51 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 50
    simpa using h
  have hprev := st134_p50
  have hstep := st134_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p52 : ((7828326398979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT134 (i+1))
      = (∑ i ∈ Finset.range 51, stT134 (i+1)) + stT134 52 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 51
    simpa using h
  have hprev := st134_p51
  have hstep := st134_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p53 : ((3990337151567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT134 (i+1))
      = (∑ i ∈ Finset.range 52, stT134 (i+1)) + stT134 53 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 52
    simpa using h
  have hprev := st134_p52
  have hstep := st134_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p54 : ((4331725099403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT134 (i+1))
      = (∑ i ∈ Finset.range 53, stT134 (i+1)) + stT134 54 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 53
    simpa using h
  have hprev := st134_p53
  have hstep := st134_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p55 : ((3701262476003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT134 (i+1))
      = (∑ i ∈ Finset.range 54, stT134 (i+1)) + stT134 55 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 54
    simpa using h
  have hprev := st134_p54
  have hstep := st134_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p56 : ((4325416264647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT134 (i+1))
      = (∑ i ∈ Finset.range 55, stT134 (i+1)) + stT134 56 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 55
    simpa using h
  have hprev := st134_p55
  have hstep := st134_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p57 : ((1011400511433/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT134 (i+1))
      = (∑ i ∈ Finset.range 56, stT134 (i+1)) + stT134 57 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 56
    simpa using h
  have hprev := st134_p56
  have hstep := st134_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p58 : ((7610279591499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT134 (i+1))
      = (∑ i ∈ Finset.range 57, stT134 (i+1)) + stT134 58 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 57
    simpa using h
  have hprev := st134_p57
  have hstep := st134_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p59 : ((1104428267577/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT134 (i+1))
      = (∑ i ∈ Finset.range 58, stT134 (i+1)) + stT134 59 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 58
    simpa using h
  have hprev := st134_p58
  have hstep := st134_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p60 : ((7731076742741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT134 (i+1))
      = (∑ i ∈ Finset.range 59, stT134 (i+1)) + stT134 60 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 59
    simpa using h
  have hprev := st134_p59
  have hstep := st134_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p61 : ((7858337639733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT134 (i+1))
      = (∑ i ∈ Finset.range 60, stT134 (i+1)) + stT134 61 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 60
    simpa using h
  have hprev := st134_p60
  have hstep := st134_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p62 : ((882328058953/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT134 (i+1))
      = (∑ i ∈ Finset.range 61, stT134 (i+1)) + stT134 62 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 61
    simpa using h
  have hprev := st134_p61
  have hstep := st134_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p63 : ((47599243589/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT134 (i+1))
      = (∑ i ∈ Finset.range 62, stT134 (i+1)) + stT134 63 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 62
    simpa using h
  have hprev := st134_p62
  have hstep := st134_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p64 : ((49529087339/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT134 (i+1))
      = (∑ i ∈ Finset.range 63, stT134 (i+1)) + stT134 64 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 63
    simpa using h
  have hprev := st134_p63
  have hstep := st134_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p65 : ((4413345684301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT134 (i+1))
      = (∑ i ∈ Finset.range 64, stT134 (i+1)) + stT134 65 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 64
    simpa using h
  have hprev := st134_p64
  have hstep := st134_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p66 : ((7665902827067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT134 (i+1))
      = (∑ i ∈ Finset.range 65, stT134 (i+1)) + stT134 66 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 65
    simpa using h
  have hprev := st134_p65
  have hstep := st134_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p67 : ((7793831292583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT134 (i+1))
      = (∑ i ∈ Finset.range 66, stT134 (i+1)) + stT134 67 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 66
    simpa using h
  have hprev := st134_p66
  have hstep := st134_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p68 : ((8846526747433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT134 (i+1))
      = (∑ i ∈ Finset.range 67, stT134 (i+1)) + stT134 68 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 67
    simpa using h
  have hprev := st134_p67
  have hstep := st134_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p69 : ((7899850553321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT134 (i+1))
      = (∑ i ∈ Finset.range 68, stT134 (i+1)) + stT134 69 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 68
    simpa using h
  have hprev := st134_p68
  have hstep := st134_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p70 : ((3768339513221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT134 (i+1))
      = (∑ i ∈ Finset.range 69, stT134 (i+1)) + stT134 70 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 69
    simpa using h
  have hprev := st134_p69
  have hstep := st134_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p71 : ((4361566237443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT134 (i+1))
      = (∑ i ∈ Finset.range 70, stT134 (i+1)) + stT134 71 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 70
    simpa using h
  have hprev := st134_p70
  have hstep := st134_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p72 : ((4173590037907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT134 (i+1))
      = (∑ i ∈ Finset.range 71, stT134 (i+1)) + stT134 72 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 71
    simpa using h
  have hprev := st134_p71
  have hstep := st134_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p73 : ((3691275542033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT134 (i+1))
      = (∑ i ∈ Finset.range 72, stT134 (i+1)) + stT134 73 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 72
    simpa using h
  have hprev := st134_p72
  have hstep := st134_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p74 : ((4129636523063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT134 (i+1))
      = (∑ i ∈ Finset.range 73, stT134 (i+1)) + stT134 74 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 73
    simpa using h
  have hprev := st134_p73
  have hstep := st134_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p75 : ((4400512977263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT134 (i+1))
      = (∑ i ∈ Finset.range 74, stT134 (i+1)) + stT134 75 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 74
    simpa using h
  have hprev := st134_p74
  have hstep := st134_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p76 : ((76999517049/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT134 (i+1))
      = (∑ i ∈ Finset.range 75, stT134 (i+1)) + stT134 76 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 75
    simpa using h
  have hprev := st134_p75
  have hstep := st134_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p77 : ((3791087282203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT134 (i+1))
      = (∑ i ∈ Finset.range 76, stT134 (i+1)) + stT134 77 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 76
    simpa using h
  have hprev := st134_p76
  have hstep := st134_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p78 : ((544543533441/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT134 (i+1))
      = (∑ i ∈ Finset.range 77, stT134 (i+1)) + stT134 78 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 77
    simpa using h
  have hprev := st134_p77
  have hstep := st134_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p79 : ((531190426513/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT134 (i+1))
      = (∑ i ∈ Finset.range 78, stT134 (i+1)) + stT134 79 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 78
    simpa using h
  have hprev := st134_p78
  have hstep := st134_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p80 : ((1858203952891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT134 (i+1))
      = (∑ i ∈ Finset.range 79, stT134 (i+1)) + stT134 80 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 79
    simpa using h
  have hprev := st134_p79
  have hstep := st134_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p81 : ((491564041077/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT134 (i+1))
      = (∑ i ∈ Finset.range 80, stT134 (i+1)) + stT134 81 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 80
    simpa using h
  have hprev := st134_p80
  have hstep := st134_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p82 : ((8848045010577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT134 (i+1))
      = (∑ i ∈ Finset.range 81, stT134 (i+1)) + stT134 82 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 81
    simpa using h
  have hprev := st134_p81
  have hstep := st134_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p83 : ((4148228176287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT134 (i+1))
      = (∑ i ∈ Finset.range 82, stT134 (i+1)) + stT134 83 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 82
    simpa using h
  have hprev := st134_p82
  have hstep := st134_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p84 : ((921529843533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT134 (i+1))
      = (∑ i ∈ Finset.range 83, stT134 (i+1)) + stT134 84 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 83
    simpa using h
  have hprev := st134_p83
  have hstep := st134_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p85 : ((497655970009/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT134 (i+1))
      = (∑ i ∈ Finset.range 84, stT134 (i+1)) + stT134 85 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 84
    simpa using h
  have hprev := st134_p84
  have hstep := st134_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p86 : ((8869149626763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT134 (i+1))
      = (∑ i ∈ Finset.range 85, stT134 (i+1)) + stT134 86 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 85
    simpa using h
  have hprev := st134_p85
  have hstep := st134_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p87 : ((4154214583599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT134 (i+1))
      = (∑ i ∈ Finset.range 86, stT134 (i+1)) + stT134 87 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 86
    simpa using h
  have hprev := st134_p86
  have hstep := st134_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p88 : ((3689264679953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT134 (i+1))
      = (∑ i ∈ Finset.range 87, stT134 (i+1)) + stT134 88 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 87
    simpa using h
  have hprev := st134_p87
  have hstep := st134_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p89 : ((3921819541777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT134 (i+1))
      = (∑ i ∈ Finset.range 88, stT134 (i+1)) + stT134 89 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 88
    simpa using h
  have hprev := st134_p88
  have hstep := st134_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p90 : ((4411100060647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT134 (i+1))
      = (∑ i ∈ Finset.range 89, stT134 (i+1)) + stT134 90 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 89
    simpa using h
  have hprev := st134_p89
  have hstep := st134_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p91 : ((8521775267999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT134 (i+1))
      = (∑ i ∈ Finset.range 90, stT134 (i+1)) + stT134 91 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 90
    simpa using h
  have hprev := st134_p90
  have hstep := st134_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p92 : ((7496807155677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT134 (i+1))
      = (∑ i ∈ Finset.range 91, stT134 (i+1)) + stT134 92 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 91
    simpa using h
  have hprev := st134_p91
  have hstep := st134_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p93 : ((1890295527677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT134 (i+1))
      = (∑ i ∈ Finset.range 92, stT134 (i+1)) + stT134 93 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 92
    simpa using h
  have hprev := st134_p92
  have hstep := st134_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p94 : ((8589617146913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT134 (i+1))
      = (∑ i ∈ Finset.range 93, stT134 (i+1)) + stT134 94 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 93
    simpa using h
  have hprev := st134_p93
  have hstep := st134_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p95 : ((1764343598797/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT134 (i+1))
      = (∑ i ∈ Finset.range 94, stT134 (i+1)) + stT134 95 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 94
    simpa using h
  have hprev := st134_p94
  have hstep := st134_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p96 : ((3939993967711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT134 (i+1))
      = (∑ i ∈ Finset.range 95, stT134 (i+1)) + stT134 96 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 95
    simpa using h
  have hprev := st134_p95
  have hstep := st134_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p97 : ((1831284845777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT134 (i+1))
      = (∑ i ∈ Finset.range 96, stT134 (i+1)) + stT134 97 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 96
    simpa using h
  have hprev := st134_p96
  have hstep := st134_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p98 : ((2011779310213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT134 (i+1))
      = (∑ i ∈ Finset.range 97, stT134 (i+1)) + stT134 98 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 97
    simpa using h
  have hprev := st134_p97
  have hstep := st134_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p99 : ((2221116456869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT134 (i+1))
      = (∑ i ∈ Finset.range 98, stT134 (i+1)) + stT134 99 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 98
    simpa using h
  have hprev := st134_p98
  have hstep := st134_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p100 : ((2132598956869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT134 (i+1))
      = (∑ i ∈ Finset.range 99, stT134 (i+1)) + stT134 100 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 99
    simpa using h
  have hprev := st134_p99
  have hstep := st134_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p101 : ((3771500357177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT134 (i+1))
      = (∑ i ∈ Finset.range 100, stT134 (i+1)) + stT134 101 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 100
    simpa using h
  have hprev := st134_p100
  have hstep := st134_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p102 : ((3709180442057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT134 (i+1))
      = (∑ i ∈ Finset.range 101, stT134 (i+1)) + stT134 102 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 101
    simpa using h
  have hprev := st134_p101
  have hstep := st134_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p103 : ((8329785282469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT134 (i+1))
      = (∑ i ∈ Finset.range 102, stT134 (i+1)) + stT134 103 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 102
    simpa using h
  have hprev := st134_p102
  have hstep := st134_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p104 : ((8935386587569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT134 (i+1))
      = (∑ i ∈ Finset.range 103, stT134 (i+1)) + stT134 104 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 103
    simpa using h
  have hprev := st134_p103
  have hstep := st134_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p105 : ((418551688709/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT134 (i+1))
      = (∑ i ∈ Finset.range 104, stT134 (i+1)) + stT134 105 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 104
    simpa using h
  have hprev := st134_p104
  have hstep := st134_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p106 : ((930970776431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT134 (i+1))
      = (∑ i ∈ Finset.range 105, stT134 (i+1)) + stT134 106 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 105
    simpa using h
  have hprev := st134_p105
  have hstep := st134_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p107 : ((931370038399/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT134 (i+1))
      = (∑ i ∈ Finset.range 106, stT134 (i+1)) + stT134 107 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 106
    simpa using h
  have hprev := st134_p106
  have hstep := st134_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p108 : ((4182017260471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT134 (i+1))
      = (∑ i ∈ Finset.range 107, stT134 (i+1)) + stT134 108 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 107
    simpa using h
  have hprev := st134_p107
  have hstep := st134_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p109 : ((4474369701321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT134 (i+1))
      = (∑ i ∈ Finset.range 108, stT134 (i+1)) + stT134 109 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 108
    simpa using h
  have hprev := st134_p108
  have hstep := st134_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p110 : ((8436532404801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT134 (i+1))
      = (∑ i ∈ Finset.range 109, stT134 (i+1)) + stT134 110 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 109
    simpa using h
  have hprev := st134_p109
  have hstep := st134_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p111 : ((7507972082559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT134 (i+1))
      = (∑ i ∈ Finset.range 110, stT134 (i+1)) + stT134 111 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 110
    simpa using h
  have hprev := st134_p110
  have hstep := st134_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p112 : ((7357336101343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT134 (i+1))
      = (∑ i ∈ Finset.range 111, stT134 (i+1)) + stT134 112 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 111
    simpa using h
  have hprev := st134_p111
  have hstep := st134_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p113 : ((8164287598783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT134 (i+1))
      = (∑ i ∈ Finset.range 112, stT134 (i+1)) + stT134 113 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 112
    simpa using h
  have hprev := st134_p112
  have hstep := st134_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p114 : ((8914967968963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT134 (i+1))
      = (∑ i ∈ Finset.range 113, stT134 (i+1)) + stT134 114 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 113
    simpa using h
  have hprev := st134_p113
  have hstep := st134_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p115 : ((2173220877667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT134 (i+1))
      = (∑ i ∈ Finset.range 114, stT134 (i+1)) + stT134 115 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 114
    simpa using h
  have hprev := st134_p114
  have hstep := st134_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p116 : ((1944444144867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT134 (i+1))
      = (∑ i ∈ Finset.range 115, stT134 (i+1)) + stT134 116 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 115
    simpa using h
  have hprev := st134_p115
  have hstep := st134_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p117 : ((1452556104783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT134 (i+1))
      = (∑ i ∈ Finset.range 116, stT134 (i+1)) + stT134 117 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 116
    simpa using h
  have hprev := st134_p116
  have hstep := st134_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p118 : ((7743640511667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT134 (i+1))
      = (∑ i ∈ Finset.range 117, stT134 (i+1)) + stT134 118 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 117
    simpa using h
  have hprev := st134_p117
  have hstep := st134_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p119 : ((8654786071881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT134 (i+1))
      = (∑ i ∈ Finset.range 118, stT134 (i+1)) + stT134 119 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 118
    simpa using h
  have hprev := st134_p118
  have hstep := st134_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p120 : ((8958981741981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT134 (i+1))
      = (∑ i ∈ Finset.range 119, stT134 (i+1)) + stT134 120 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 119
    simpa using h
  have hprev := st134_p119
  have hstep := st134_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p121 : ((4162306748363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT134 (i+1))
      = (∑ i ∈ Finset.range 120, stT134 (i+1)) + stT134 121 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 120
    simpa using h
  have hprev := st134_p120
  have hstep := st134_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p122 : ((746081867179/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT134 (i+1))
      = (∑ i ∈ Finset.range 121, stT134 (i+1)) + stT134 122 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 121
    simpa using h
  have hprev := st134_p121
  have hstep := st134_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p123 : ((365297436713/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT134 (i+1))
      = (∑ i ∈ Finset.range 122, stT134 (i+1)) + stT134 123 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 122
    simpa using h
  have hprev := st134_p122
  have hstep := st134_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p124 : ((4008126138623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT134 (i+1))
      = (∑ i ∈ Finset.range 123, stT134 (i+1)) + stT134 124 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 123
    simpa using h
  have hprev := st134_p123
  have hstep := st134_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p125 : ((8833634229893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT134 (i+1))
      = (∑ i ∈ Finset.range 124, stT134 (i+1)) + stT134 125 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 124
    simpa using h
  have hprev := st134_p124
  have hstep := st134_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p126 : ((8909292255513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT134 (i+1))
      = (∑ i ∈ Finset.range 125, stT134 (i+1)) + stT134 126 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 125
    simpa using h
  have hprev := st134_p125
  have hstep := st134_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p127 : ((2043794343157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT134 (i+1))
      = (∑ i ∈ Finset.range 126, stT134 (i+1)) + stT134 127 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 126
    simpa using h
  have hprev := st134_p126
  have hstep := st134_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p128 : ((1845235105861/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT134 (i+1))
      = (∑ i ∈ Finset.range 127, stT134 (i+1)) + stT134 128 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 127
    simpa using h
  have hprev := st134_p127
  have hstep := st134_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p129 : ((1829041851069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT134 (i+1))
      = (∑ i ∈ Finset.range 128, stT134 (i+1)) + stT134 129 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 128
    simpa using h
  have hprev := st134_p128
  have hstep := st134_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p130 : ((401759328457/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT134 (i+1))
      = (∑ i ∈ Finset.range 129, stT134 (i+1)) + stT134 130 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 129
    simpa using h
  have hprev := st134_p129
  have hstep := st134_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p131 : ((2208477104539/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT134 (i+1))
      = (∑ i ∈ Finset.range 130, stT134 (i+1)) + stT134 131 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 130
    simpa using h
  have hprev := st134_p130
  have hstep := st134_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p132 : ((447532590991/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT134 (i+1))
      = (∑ i ∈ Finset.range 131, stT134 (i+1)) + stT134 132 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 131
    simpa using h
  have hprev := st134_p131
  have hstep := st134_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p133 : ((414204871297/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT134 (i+1))
      = (∑ i ∈ Finset.range 132, stT134 (i+1)) + stT134 133 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 132
    simpa using h
  have hprev := st134_p132
  have hstep := st134_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p134 : ((3730640604279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT134 (i+1))
      = (∑ i ∈ Finset.range 133, stT134 (i+1)) + stT134 134 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 133
    simpa using h
  have hprev := st134_p133
  have hstep := st134_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p135 : ((7235970823777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT134 (i+1))
      = (∑ i ∈ Finset.range 134, stT134 (i+1)) + stT134 135 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 134
    simpa using h
  have hprev := st134_p134
  have hstep := st134_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p136 : ((7803990674417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT134 (i+1))
      = (∑ i ∈ Finset.range 135, stT134 (i+1)) + stT134 136 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 135
    simpa using h
  have hprev := st134_p135
  have hstep := st134_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p137 : ((8650530307867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT134 (i+1))
      = (∑ i ∈ Finset.range 136, stT134 (i+1)) + stT134 137 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 136
    simpa using h
  have hprev := st134_p136
  have hstep := st134_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p138 : ((9029347740427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT134 (i+1))
      = (∑ i ∈ Finset.range 137, stT134 (i+1)) + stT134 138 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 137
    simpa using h
  have hprev := st134_p137
  have hstep := st134_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p139 : ((8617996431963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT134 (i+1))
      = (∑ i ∈ Finset.range 138, stT134 (i+1)) + stT134 139 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 138
    simpa using h
  have hprev := st134_p138
  have hstep := st134_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p140 : ((1944340118937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT134 (i+1))
      = (∑ i ∈ Finset.range 139, stT134 (i+1)) + stT134 140 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 139
    simpa using h
  have hprev := st134_p139
  have hstep := st134_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p141 : ((361069049451/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT134 (i+1))
      = (∑ i ∈ Finset.range 140, stT134 (i+1)) + stT134 141 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 140
    simpa using h
  have hprev := st134_p140
  have hstep := st134_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p142 : ((7409385225993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT134 (i+1))
      = (∑ i ∈ Finset.range 141, stT134 (i+1)) + stT134 142 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 141
    simpa using h
  have hprev := st134_p141
  have hstep := st134_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p143 : ((8178120754301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT134 (i+1))
      = (∑ i ∈ Finset.range 142, stT134 (i+1)) + stT134 143 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 142
    simpa using h
  have hprev := st134_p142
  have hstep := st134_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p144 : ((8897355466607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT134 (i+1))
      = (∑ i ∈ Finset.range 143, stT134 (i+1)) + stT134 144 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 143
    simpa using h
  have hprev := st134_p143
  have hstep := st134_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p145 : ((8991857809991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT134 (i+1))
      = (∑ i ∈ Finset.range 144, stT134 (i+1)) + stT134 145 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 144
    simpa using h
  have hprev := st134_p144
  have hstep := st134_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p146 : ((8394178136517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT134 (i+1))
      = (∑ i ∈ Finset.range 145, stT134 (i+1)) + stT134 146 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 145
    simpa using h
  have hprev := st134_p145
  have hstep := st134_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p147 : ((3789351903267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT134 (i+1))
      = (∑ i ∈ Finset.range 146, stT134 (i+1)) + stT134 147 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 146
    simpa using h
  have hprev := st134_p146
  have hstep := st134_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p148 : ((897032498313/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT134 (i+1))
      = (∑ i ∈ Finset.range 147, stT134 (i+1)) + stT134 148 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 147
    simpa using h
  have hprev := st134_p147
  have hstep := st134_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p149 : ((936036086223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT134 (i+1))
      = (∑ i ∈ Finset.range 148, stT134 (i+1)) + stT134 149 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 148
    simpa using h
  have hprev := st134_p148
  have hstep := st134_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p150 : ((1034013769107/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT134 (i+1))
      = (∑ i ∈ Finset.range 149, stT134 (i+1)) + stT134 150 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 149
    simpa using h
  have hprev := st134_p149
  have hstep := st134_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p151 : ((2235156603903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT134 (i+1))
      = (∑ i ∈ Finset.range 150, stT134 (i+1)) + stT134 151 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 150
    simpa using h
  have hprev := st134_p150
  have hstep := st134_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p152 : ((9005087522223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT134 (i+1))
      = (∑ i ∈ Finset.range 151, stT134 (i+1)) + stT134 152 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 151
    simpa using h
  have hprev := st134_p151
  have hstep := st134_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p153 : ((8425614282319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT134 (i+1))
      = (∑ i ∈ Finset.range 152, stT134 (i+1)) + stT134 153 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 152
    simpa using h
  have hprev := st134_p152
  have hstep := st134_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p154 : ((304955136663/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT134 (i+1))
      = (∑ i ∈ Finset.range 153, stT134 (i+1)) + stT134 154 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 153
    simpa using h
  have hprev := st134_p153
  have hstep := st134_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p155 : ((1433766680571/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT134 (i+1))
      = (∑ i ∈ Finset.range 154, stT134 (i+1)) + stT134 155 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 154
    simpa using h
  have hprev := st134_p154
  have hstep := st134_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p156 : ((294969920127/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT134 (i+1))
      = (∑ i ∈ Finset.range 155, stT134 (i+1)) + stT134 156 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 155
    simpa using h
  have hprev := st134_p155
  have hstep := st134_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p157 : ((8091081665601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT134 (i+1))
      = (∑ i ∈ Finset.range 156, stT134 (i+1)) + stT134 157 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 156
    simpa using h
  have hprev := st134_p156
  have hstep := st134_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p158 : ((551569343229/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT134 (i+1))
      = (∑ i ∈ Finset.range 157, stT134 (i+1)) + stT134 158 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 157
    simpa using h
  have hprev := st134_p157
  have hstep := st134_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p159 : ((1816353075969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT134 (i+1))
      = (∑ i ∈ Finset.range 158, stT134 (i+1)) + stT134 159 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 158
    simpa using h
  have hprev := st134_p158
  have hstep := st134_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p160 : ((1739087191361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT134 (i+1))
      = (∑ i ∈ Finset.range 159, stT134 (i+1)) + stT134 160 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 159
    simpa using h
  have hprev := st134_p159
  have hstep := st134_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p161 : ((7927220819/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT134 (i+1))
      = (∑ i ∈ Finset.range 160, stT134 (i+1)) + stT134 161 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 160
    simpa using h
  have hprev := st134_p160
  have hstep := st134_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p162 : ((145613242971/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT134 (i+1))
      = (∑ i ∈ Finset.range 161, stT134 (i+1)) + stT134 162 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 161
    simpa using h
  have hprev := st134_p161
  have hstep := st134_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p163 : ((716989337793/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT134 (i+1))
      = (∑ i ∈ Finset.range 162, stT134 (i+1)) + stT134 163 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 162
    simpa using h
  have hprev := st134_p162
  have hstep := st134_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p164 : ((3829738265247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT134 (i+1))
      = (∑ i ∈ Finset.range 163, stT134 (i+1)) + stT134 164 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 163
    simpa using h
  have hprev := st134_p163
  have hstep := st134_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p165 : ((6748431511/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT134 (i+1))
      = (∑ i ∈ Finset.range 164, stT134 (i+1)) + stT134 165 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 164
    simpa using h
  have hprev := st134_p164
  have hstep := st134_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p166 : ((9013254999/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT134 (i+1))
      = (∑ i ∈ Finset.range 165, stT134 (i+1)) + stT134 166 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 165
    simpa using h
  have hprev := st134_p165
  have hstep := st134_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p167 : ((9040136836197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT134 (i+1))
      = (∑ i ∈ Finset.range 166, stT134 (i+1)) + stT134 167 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 166
    simpa using h
  have hprev := st134_p166
  have hstep := st134_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p168 : ((8505683864787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT134 (i+1))
      = (∑ i ∈ Finset.range 167, stT134 (i+1)) + stT134 168 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 167
    simpa using h
  have hprev := st134_p167
  have hstep := st134_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p169 : ((12088211207/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT134 (i+1))
      = (∑ i ∈ Finset.range 168, stT134 (i+1)) + stT134 169 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 168
    simpa using h
  have hprev := st134_p168
  have hstep := st134_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p170 : ((719129184869/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT134 (i+1))
      = (∑ i ∈ Finset.range 169, stT134 (i+1)) + stT134 170 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 169
    simpa using h
  have hprev := st134_p169
  have hstep := st134_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p171 : ((718769842941/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT134 (i+1))
      = (∑ i ∈ Finset.range 170, stT134 (i+1)) + stT134 171 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 170
    simpa using h
  have hprev := st134_p170
  have hstep := st134_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p172 : ((3861054623709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT134 (i+1))
      = (∑ i ∈ Finset.range 171, stT134 (i+1)) + stT134 172 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 171
    simpa using h
  have hprev := st134_p171
  have hstep := st134_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p173 : ((4241121095209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT134 (i+1))
      = (∑ i ∈ Finset.range 172, stT134 (i+1)) + stT134 173 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 172
    simpa using h
  have hprev := st134_p172
  have hstep := st134_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p174 : ((4517141544617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT134 (i+1))
      = (∑ i ∈ Finset.range 173, stT134 (i+1)) + stT134 174 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 173
    simpa using h
  have hprev := st134_p173
  have hstep := st134_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p175 : ((181407905633/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT134 (i+1))
      = (∑ i ∈ Finset.range 174, stT134 (i+1)) + stT134 175 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 174
    simpa using h
  have hprev := st134_p174
  have hstep := st134_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p176 : ((214394325991/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT134 (i+1))
      = (∑ i ∈ Finset.range 175, stT134 (i+1)) + stT134 176 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 175
    simpa using h
  have hprev := st134_p175
  have hstep := st134_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p177 : ((978442690451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT134 (i+1))
      = (∑ i ∈ Finset.range 176, stT134 (i+1)) + stT134 177 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 176
    simpa using h
  have hprev := st134_p176
  have hstep := st134_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p178 : ((361746989399/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT134 (i+1))
      = (∑ i ∈ Finset.range 177, stT134 (i+1)) + stT134 178 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 177
    simpa using h
  have hprev := st134_p177
  have hstep := st134_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p179 : ((355752552679/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT134 (i+1))
      = (∑ i ∈ Finset.range 178, stT134 (i+1)) + stT134 179 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 178
    simpa using h
  have hprev := st134_p178
  have hstep := st134_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p180 : ((2940191213/3906250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT134 (i+1))
      = (∑ i ∈ Finset.range 179, stT134 (i+1)) + stT134 180 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 179
    simpa using h
  have hprev := st134_p179
  have hstep := st134_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p181 : ((824831951227/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT134 (i+1))
      = (∑ i ∈ Finset.range 180, stT134 (i+1)) + stT134 181 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 180
    simpa using h
  have hprev := st134_p180
  have hstep := st134_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p182 : ((1780087405253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT134 (i+1))
      = (∑ i ∈ Finset.range 181, stT134 (i+1)) + stT134 182 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 181
    simpa using h
  have hprev := st134_p181
  have hstep := st134_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p183 : ((2286938994643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT134 (i+1))
      = (∑ i ∈ Finset.range 182, stT134 (i+1)) + stT134 183 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 182
    simpa using h
  have hprev := st134_p182
  have hstep := st134_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p184 : ((17320487241/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT134 (i+1))
      = (∑ i ∈ Finset.range 183, stT134 (i+1)) + stT134 184 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 183
    simpa using h
  have hprev := st134_p183
  have hstep := st134_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p185 : ((8207784788527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT134 (i+1))
      = (∑ i ∈ Finset.range 184, stT134 (i+1)) + stT134 185 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 184
    simpa using h
  have hprev := st134_p184
  have hstep := st134_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p186 : ((7500476013487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT134 (i+1))
      = (∑ i ∈ Finset.range 185, stT134 (i+1)) + stT134 186 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 185
    simpa using h
  have hprev := st134_p185
  have hstep := st134_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p187 : ((1774100402697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT134 (i+1))
      = (∑ i ∈ Finset.range 186, stT134 (i+1)) + stT134 187 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 186
    simpa using h
  have hprev := st134_p186
  have hstep := st134_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p188 : ((1797598492653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT134 (i+1))
      = (∑ i ∈ Finset.range 187, stT134 (i+1)) + stT134 188 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 187
    simpa using h
  have hprev := st134_p187
  have hstep := st134_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p189 : ((1933021789341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT134 (i+1))
      = (∑ i ∈ Finset.range 188, stT134 (i+1)) + stT134 189 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 188
    simpa using h
  have hprev := st134_p188
  have hstep := st134_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p190 : ((2114331663047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT134 (i+1))
      = (∑ i ∈ Finset.range 189, stT134 (i+1)) + stT134 190 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 189
    simpa using h
  have hprev := st134_p189
  have hstep := st134_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p191 : ((4509981299767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT134 (i+1))
      = (∑ i ∈ Finset.range 190, stT134 (i+1)) + stT134 191 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 190
    simpa using h
  have hprev := st134_p190
  have hstep := st134_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p192 : ((9157039106627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT134 (i+1))
      = (∑ i ∈ Finset.range 191, stT134 (i+1)) + stT134 192 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 191
    simpa using h
  have hprev := st134_p191
  have hstep := st134_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p193 : ((8808780608771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT134 (i+1))
      = (∑ i ∈ Finset.range 192, stT134 (i+1)) + stT134 193 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 192
    simpa using h
  have hprev := st134_p192
  have hstep := st134_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p194 : ((4070120440309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT134 (i+1))
      = (∑ i ∈ Finset.range 193, stT134 (i+1)) + stT134 194 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 193
    simpa using h
  have hprev := st134_p193
  have hstep := st134_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p195 : ((3729730929589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT134 (i+1))
      = (∑ i ∈ Finset.range 194, stT134 (i+1)) + stT134 195 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 194
    simpa using h
  have hprev := st134_p194
  have hstep := st134_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p196 : ((707412027647/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT134 (i+1))
      = (∑ i ∈ Finset.range 195, stT134 (i+1)) + stT134 196 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 195
    simpa using h
  have hprev := st134_p195
  have hstep := st134_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p197 : ((357692176603/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT134 (i+1))
      = (∑ i ∈ Finset.range 196, stT134 (i+1)) + stT134 197 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 196
    simpa using h
  have hprev := st134_p196
  have hstep := st134_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p198 : ((7658966447859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT134 (i+1))
      = (∑ i ∈ Finset.range 197, stT134 (i+1)) + stT134 198 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 197
    simpa using h
  have hprev := st134_p197
  have hstep := st134_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p199 : ((334556129359/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT134 (i+1))
      = (∑ i ∈ Finset.range 198, stT134 (i+1)) + stT134 199 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 198
    simpa using h
  have hprev := st134_p198
  have hstep := st134_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p200 : ((8960472302737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT134 (i+1))
      = (∑ i ∈ Finset.range 199, stT134 (i+1)) + stT134 200 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 199
    simpa using h
  have hprev := st134_p199
  have hstep := st134_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p201 : ((9192898997827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT134 (i+1))
      = (∑ i ∈ Finset.range 200, stT134 (i+1)) + stT134 201 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 200
    simpa using h
  have hprev := st134_p200
  have hstep := st134_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p202 : ((8965432096809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT134 (i+1))
      = (∑ i ∈ Finset.range 201, stT134 (i+1)) + stT134 202 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 201
    simpa using h
  have hprev := st134_p201
  have hstep := st134_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p203 : ((4189140441833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT134 (i+1))
      = (∑ i ∈ Finset.range 202, stT134 (i+1)) + stT134 203 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 202
    simpa using h
  have hprev := st134_p202
  have hstep := st134_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p204 : ((7680264811601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT134 (i+1))
      = (∑ i ∈ Finset.range 203, stT134 (i+1)) + stT134 204 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 203
    simpa using h
  have hprev := st134_p203
  have hstep := st134_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p205 : ((3580780879631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT134 (i+1))
      = (∑ i ∈ Finset.range 204, stT134 (i+1)) + stT134 205 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 204
    simpa using h
  have hprev := st134_p204
  have hstep := st134_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p206 : ((3516716188331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT134 (i+1))
      = (∑ i ∈ Finset.range 205, stT134 (i+1)) + stT134 206 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 205
    simpa using h
  have hprev := st134_p205
  have hstep := st134_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p207 : ((3672227965471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT134 (i+1))
      = (∑ i ∈ Finset.range 206, stT134 (i+1)) + stT134 207 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 206
    simpa using h
  have hprev := st134_p206
  have hstep := st134_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p208 : ((7965412765817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT134 (i+1))
      = (∑ i ∈ Finset.range 207, stT134 (i+1)) + stT134 208 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 207
    simpa using h
  have hprev := st134_p207
  have hstep := st134_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p209 : ((8645706567677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT134 (i+1))
      = (∑ i ∈ Finset.range 208, stT134 (i+1)) + stT134 209 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 208
    simpa using h
  have hprev := st134_p208
  have hstep := st134_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p210 : ((4557893908261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT134 (i+1))
      = (∑ i ∈ Finset.range 209, stT134 (i+1)) + stT134 210 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 209
    simpa using h
  have hprev := st134_p209
  have hstep := st134_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p211 : ((4596658256299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT134 (i+1))
      = (∑ i ∈ Finset.range 210, stT134 (i+1)) + stT134 211 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 210
    simpa using h
  have hprev := st134_p210
  have hstep := st134_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p212 : ((2212907661623/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT134 (i+1))
      = (∑ i ∈ Finset.range 211, stT134 (i+1)) + stT134 212 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 211
    simpa using h
  have hprev := st134_p211
  have hstep := st134_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p213 : ((64264305377/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT134 (i+1))
      = (∑ i ∈ Finset.range 212, stT134 (i+1)) + stT134 213 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 212
    simpa using h
  have hprev := st134_p212
  have hstep := st134_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p214 : ((188923964833/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT134 (i+1))
      = (∑ i ∈ Finset.range 213, stT134 (i+1)) + stT134 214 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 213
    simpa using h
  have hprev := st134_p213
  have hstep := st134_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p215 : ((709807552959/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT134 (i+1))
      = (∑ i ∈ Finset.range 214, stT134 (i+1)) + stT134 215 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 214
    simpa using h
  have hprev := st134_p214
  have hstep := st134_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p216 : ((3509584639419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT134 (i+1))
      = (∑ i ∈ Finset.range 215, stT134 (i+1)) + stT134 216 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 215
    simpa using h
  have hprev := st134_p215
  have hstep := st134_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p217 : ((3673115104221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT134 (i+1))
      = (∑ i ∈ Finset.range 216, stT134 (i+1)) + stT134 217 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 216
    simpa using h
  have hprev := st134_p216
  have hstep := st134_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p218 : ((7955479898337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT134 (i+1))
      = (∑ i ∈ Finset.range 217, stT134 (i+1)) + stT134 218 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 217
    simpa using h
  have hprev := st134_p217
  have hstep := st134_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p219 : ((4311204333271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT134 (i+1))
      = (∑ i ∈ Finset.range 218, stT134 (i+1)) + stT134 219 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 218
    simpa using h
  have hprev := st134_p218
  have hstep := st134_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p220 : ((9105541692539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT134 (i+1))
      = (∑ i ∈ Finset.range 219, stT134 (i+1)) + stT134 220 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 219
    simpa using h
  have hprev := st134_p219
  have hstep := st134_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p221 : ((9233390405531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT134 (i+1))
      = (∑ i ∈ Finset.range 220, stT134 (i+1)) + stT134 221 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 220
    simpa using h
  have hprev := st134_p220
  have hstep := st134_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p222 : ((179271262867/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT134 (i+1))
      = (∑ i ∈ Finset.range 221, stT134 (i+1)) + stT134 222 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 221
    simpa using h
  have hprev := st134_p221
  have hstep := st134_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p223 : ((83943465807/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT134 (i+1))
      = (∑ i ∈ Finset.range 222, stT134 (i+1)) + stT134 223 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 222
    simpa using h
  have hprev := st134_p222
  have hstep := st134_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p224 : ((1931706497673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT134 (i+1))
      = (∑ i ∈ Finset.range 223, stT134 (i+1)) + stT134 224 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 223
    simpa using h
  have hprev := st134_p223
  have hstep := st134_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p225 : ((57541533789/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT134 (i+1))
      = (∑ i ∈ Finset.range 224, stT134 (i+1)) + stT134 225 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 224
    simpa using h
  have hprev := st134_p224
  have hstep := st134_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p226 : ((6973972931679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT134 (i+1))
      = (∑ i ∈ Finset.range 225, stT134 (i+1)) + stT134 226 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 225
    simpa using h
  have hprev := st134_p225
  have hstep := st134_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p227 : ((3571203954279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT134 (i+1))
      = (∑ i ∈ Finset.range 226, stT134 (i+1)) + stT134 227 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 226
    simpa using h
  have hprev := st134_p226
  have hstep := st134_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p228 : ((3819006010297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT134 (i+1))
      = (∑ i ∈ Finset.range 227, stT134 (i+1)) + stT134 228 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 227
    simpa using h
  have hprev := st134_p227
  have hstep := st134_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p229 : ((4146224580993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT134 (i+1))
      = (∑ i ∈ Finset.range 228, stT134 (i+1)) + stT134 229 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 228
    simpa using h
  have hprev := st134_p228
  have hstep := st134_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p230 : ((4443767168473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT134 (i+1))
      = (∑ i ∈ Finset.range 229, stT134 (i+1)) + stT134 230 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 229
    simpa using h
  have hprev := st134_p229
  have hstep := st134_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p231 : ((9228195704657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT134 (i+1))
      = (∑ i ∈ Finset.range 230, stT134 (i+1)) + stT134 231 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 230
    simpa using h
  have hprev := st134_p230
  have hstep := st134_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p232 : ((184109869001/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT134 (i+1))
      = (∑ i ∈ Finset.range 231, stT134 (i+1)) + stT134 232 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 231
    simpa using h
  have hprev := st134_p231
  have hstep := st134_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p233 : ((275927769089/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT134 (i+1))
      = (∑ i ∈ Finset.range 232, stT134 (i+1)) + stT134 233 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 232
    simpa using h
  have hprev := st134_p232
  have hstep := st134_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p234 : ((8224041599467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT134 (i+1))
      = (∑ i ∈ Finset.range 233, stT134 (i+1)) + stT134 234 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 233
    simpa using h
  have hprev := st134_p233
  have hstep := st134_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p235 : ((758285894509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT134 (i+1))
      = (∑ i ∈ Finset.range 234, stT134 (i+1)) + stT134 235 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 234
    simpa using h
  have hprev := st134_p234
  have hstep := st134_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p236 : ((1421699028859/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT134 (i+1))
      = (∑ i ∈ Finset.range 235, stT134 (i+1)) + stT134 236 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 235
    simpa using h
  have hprev := st134_p235
  have hstep := st134_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p237 : ((1389576233391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT134 (i+1))
      = (∑ i ∈ Finset.range 236, stT134 (i+1)) + stT134 237 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 236
    simpa using h
  have hprev := st134_p236
  have hstep := st134_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p238 : ((3574153091379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT134 (i+1))
      = (∑ i ∈ Finset.range 237, stT134 (i+1)) + stT134 238 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 237
    simpa using h
  have hprev := st134_p237
  have hstep := st134_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p239 : ((382263801201/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT134 (i+1))
      = (∑ i ∈ Finset.range 238, stT134 (i+1)) + stT134 239 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 238
    simpa using h
  have hprev := st134_p238
  have hstep := st134_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p240 : ((4142432072241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT134 (i+1))
      = (∑ i ∈ Finset.range 239, stT134 (i+1)) + stT134 240 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 239
    simpa using h
  have hprev := st134_p239
  have hstep := st134_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p241 : ((4436220995267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT134 (i+1))
      = (∑ i ∈ Finset.range 240, stT134 (i+1)) + stT134 241 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 240
    simpa using h
  have hprev := st134_p240
  have hstep := st134_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p242 : ((4616038474199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT134 (i+1))
      = (∑ i ∈ Finset.range 241, stT134 (i+1)) + stT134 242 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 241
    simpa using h
  have hprev := st134_p241
  have hstep := st134_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p243 : ((4629239902699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT134 (i+1))
      = (∑ i ∈ Finset.range 242, stT134 (i+1)) + stT134 243 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 242
    simpa using h
  have hprev := st134_p242
  have hstep := st134_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p244 : ((2236607967527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT134 (i+1))
      = (∑ i ∈ Finset.range 243, stT134 (i+1)) + stT134 244 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 243
    simpa using h
  have hprev := st134_p243
  have hstep := st134_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p245 : ((4194983084923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT134 (i+1))
      = (∑ i ∈ Finset.range 244, stT134 (i+1)) + stT134 245 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 244
    simpa using h
  have hprev := st134_p244
  have hstep := st134_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p246 : ((3876343777941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT134 (i+1))
      = (∑ i ∈ Finset.range 245, stT134 (i+1)) + stT134 246 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 245
    simpa using h
  have hprev := st134_p245
  have hstep := st134_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p247 : ((7218963426177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT134 (i+1))
      = (∑ i ∈ Finset.range 246, stT134 (i+1)) + stT134 247 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 246
    simpa using h
  have hprev := st134_p246
  have hstep := st134_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p248 : ((216896089779/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT134 (i+1))
      = (∑ i ∈ Finset.range 247, stT134 (i+1)) + stT134 248 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 247
    simpa using h
  have hprev := st134_p247
  have hstep := st134_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p249 : ((109294462507/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT134 (i+1))
      = (∑ i ∈ Finset.range 248, stT134 (i+1)) + stT134 249 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 248
    simpa using h
  have hprev := st134_p248
  have hstep := st134_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_p250 : ((7363691459083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT134 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT134 (i+1))
      = (∑ i ∈ Finset.range 249, stT134 (i+1)) + stT134 250 := by
    have h := Finset.sum_range_succ (fun i => stT134 (i+1)) 249
    simpa using h
  have hprev := st134_p249
  have hstep := st134_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st134_s250 :
    |Real.sin (((134 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))
      - ((-162459/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -237019/1000000) (δ := 3377/500000000) (ψ := -592023/1000000) 134 118
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 134`** (evaluated boundary). -/
theorem station_134_sign : 0 < hardyG ((((134:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 134 250 (by norm_num) (by norm_num)
    ((-592023/1000000 : ℚ) : ℝ)
  have hchain := st134_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT134 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((134 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-592023/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st134_c250
  have hsinb := abs_le.mp st134_s250
  have hbdy_lo : ((27460989034233/287300000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((134 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ))) / 2
          - ((((134:ℕ)):ℝ))
            * Real.sin (((134 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-592023/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((134:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((134:ℝ) * Real.log (250:ℝ) - ((-592023/1000000 : ℚ) : ℝ))) / 2
        - ((134:ℝ)) * Real.sin ((134:ℝ) * Real.log (250:ℝ) - ((-592023/1000000 : ℚ) : ℝ))
        ≥ ((217098363/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((134:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((217098363/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((217098363/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((217098363/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((134:ℕ)):ℝ))+1) * (((((134:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((6578253913/15625000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((7363691459083/10000000000000 : ℚ) : ℝ) + ((27460989034233/287300000000000 : ℚ) : ℝ)
      - ((6578253913/15625000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-592023/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((134:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-592023/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((134:ℕ)):ℝ)))).re
      - Real.sin ((-592023/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((134:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((134:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((134:ℕ)):ℝ))
      = (((((134:ℕ)):ℝ)) * (Real.log ((((134:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((134:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_134
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
  have hθwin : |(((-592023/1000000 : ℚ) : ℝ) + ((22:ℤ)) * (2*Real.pi)) - theta ((((134:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((134:ℕ)):ℝ)))
    (φ := ((-592023/1000000 : ℚ) : ℝ) + ((22:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-592023/1000000 : ℚ)) : ℝ) 22).1,
    (cos_sin_shift (((-592023/1000000 : ℚ)) : ℝ) 22).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_134_sign
end AxiomAudit
