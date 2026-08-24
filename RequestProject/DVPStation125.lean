import RequestProject.DVPSqrtTable
import RequestProject.DVPLog200Table

/-!
# Station `t = 125` of the extended Hardy ladder (rung-126)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT125 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((125 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))

theorem st125_c1 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-16611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4134867/10000000) (δ := 21/100000000) (ψ := -1653947/1000000) 125 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t1 : ((-166210016621/2000000000000 : ℚ) : ℝ) ≤ stT125 1 := by
  have hc : ((-16621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).2
  have h0 : (0:ℝ) ≤ ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166210016621/2000000000000 : ℚ) : ℝ)
      = ((10000001/10000000 : ℚ) : ℝ) * ((-16621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c2 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((236287/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1331/16000) (δ := 491/50000000) (ψ := -1653947/1000000) 125 14
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t2 : ((3341425639783/5000000000000 : ℚ) : ℝ) ≤ stT125 2 := by
  have hc : ((472549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3341425639783/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((472549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c3 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((182853/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375203/2000000) (δ := 1077/100000000) (ψ := -1653947/1000000) 125 22
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t3 : ((1055629992431/2500000000000 : ℚ) : ℝ) ≤ stT125 3 := by
  have hc : ((365681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1055629992431/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((365681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c4 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((137497/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2471117/10000000) (δ := 183/25000000) (ψ := -1653947/1000000) 125 28
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t4 : ((274969/1000000 : ℚ) : ℝ) ≤ stT125 4 := by
  have hc : ((274969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274969/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((274969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c5 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-19961/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 442939/1000000) (δ := 1119/100000000) (ψ := -1653947/1000000) 125 32
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t5 : ((-5580666711/62500000000 : ℚ) : ℝ) ≤ stT125 5 := by
  have hc : ((-9983/50000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5580666711/62500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-9983/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c6 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((420737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1426977/10000000) (δ := 827/100000000) (ψ := -1653947/1000000) 125 36
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t6 : ((107346822949/312500000000 : ℚ) : ℝ) ≤ stT125 6 := by
  have hc : ((52589/62500 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107346822949/312500000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((52589/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c7 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((15446/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378779/10000000) (δ := 663/100000000) (ψ := -1653947/1000000) 125 39
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t7 : ((467019427017/1250000000000 : ℚ) : ℝ) ≤ stT125 7 := by
  have hc : ((494247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467019427017/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((494247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c8 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-168359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1443527/2500000) (δ := 731/100000000) (ψ := -1653947/1000000) 125 42
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t8 : ((-595283162881/2500000000000 : ℚ) : ℝ) ≤ stT125 8 := by
  have hc : ((-336743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-595283162881/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-336743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c9 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((494149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95709/2500000) (δ := 963/100000000) (ψ := -1653947/1000000) 125 44
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t9 : ((411769958823/1250000000000 : ℚ) : ℝ) ≤ stT125 9 := by
  have hc : ((123531/125000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411769958823/1250000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((123531/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c10 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((225051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 563199/5000000) (δ := 227/20000000) (ψ := -1653947/1000000) 125 46
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t10 : ((1423268145329/5000000000000 : ℚ) : ℝ) ≤ stT125 10 := by
  have hc : ((450077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1423268145329/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((450077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c11 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((979659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -505097/10000000) (δ := 7/781250) (ψ := -1653947/1000000) 125 48
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t11 : ((2953631830817/10000000000000 : ℚ) : ℝ) ≤ stT125 11 := by
  have hc : ((979609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2953631830817/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((979609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c12 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-315697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295623/625000) (δ := 159/25000000) (ψ := -1653947/1000000) 125 50
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t12 : ((-28483852617/312500000000 : ℚ) : ℝ) ≤ stT125 12 := by
  have hc : ((-315747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28483852617/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-315747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c13 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-256471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 915083/2000000) (δ := 359/50000000) (ψ := -1653947/1000000) 125 51
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t13 : ((-711461250021/10000000000000 : ℚ) : ℝ) ≤ stT125 13 := by
  have hc : ((-256521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-711461250021/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-256521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c14 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((97931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3681771/10000000) (δ := 913/100000000) (ψ := -1653947/1000000) 125 53
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t14 : ((65399483793/2500000000000 : ℚ) : ℝ) ≤ stT125 14 := by
  have hc : ((97881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65399483793/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((97881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c15 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((64619/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1085269/5000000) (δ := 1273/100000000) (ψ := -1653947/1000000) 125 54
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t15 : ((20854071579/125000000000 : ℚ) : ℝ) ≤ stT125 15 := by
  have hc : ((32307/50000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20854071579/125000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((32307/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c16 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-882687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6630863/10000000) (δ := 31/3125000) (ψ := -1653947/1000000) 125 55
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t16 : ((-2206843382737/10000000000000 : ℚ) : ℝ) ≤ stT125 16 := by
  have hc : ((-882737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2206843382737/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-882737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c17 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-346323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5839869/10000000) (δ := 711/100000000) (ψ := -1653947/1000000) 125 57
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t17 : ((-210004386559/1250000000000 : ℚ) : ℝ) ≤ stT125 17 := by
  have hc : ((-86587/125000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210004386559/1250000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-86587/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c18 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((24079/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -921457/2500000) (δ := 713/100000000) (ψ := -1653947/1000000) 125 58
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t18 : ((56725269963/2500000000000 : ℚ) : ℝ) ≤ stT125 18 := by
  have hc : ((48133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56725269963/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((48133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c19 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((67631/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -499557/2000000) (δ := 241/25000000) (ψ := -1653947/1000000) 125 59
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t19 : ((620567174343/5000000000000 : ℚ) : ℝ) ≤ stT125 19 := by
  have hc : ((270499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((620567174343/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((270499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c20 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((644339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1088297/5000000) (δ := 177/20000000) (ψ := -1653947/1000000) 125 60
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t20 : ((1440673371363/10000000000000 : ℚ) : ℝ) ≤ stT125 20 := by
  have hc : ((644289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1440673371363/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((644289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c21 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((246591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2637631/10000000) (δ := 409/50000000) (ψ := -1653947/1000000) 125 61
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t21 : ((134512725187/1250000000000 : ℚ) : ℝ) ≤ stT125 21 := by
  have hc : ((123283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134512725187/1250000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((123283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c22 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((47543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3808089/10000000) (δ := 323/50000000) (ψ := -1653947/1000000) 125 62
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t22 : ((101255408451/10000000000000 : ℚ) : ℝ) ≤ stT125 22 := by
  have hc : ((47493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101255408451/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((47493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c23 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-125627/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1406219/2500000) (δ := 33/3125000) (ψ := -1653947/1000000) 125 63
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t23 : ((-52394272473/400000000000 : ℚ) : ℝ) ≤ stT125 23 := by
  have hc : ((-125637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52394272473/400000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-125637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c24 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-498719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7675003/10000000) (δ := 7/781250) (ψ := -1653947/1000000) 125 63
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t24 : ((-63628575003/312500000000 : ℚ) : ℝ) ≤ stT125 24 := by
  have hc : ((-62343/62500 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63628575003/312500000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-62343/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c25 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-156699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4723913/10000000) (δ := 483/50000000) (ψ := -1653947/1000000) 125 64
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t25 : ((-78362039181/1250000000000 : ℚ) : ℝ) ≤ stT125 25 := by
  have hc : ((-39181/125000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78362039181/1250000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-39181/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c26 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((873247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1272423/10000000) (δ := 157/20000000) (ψ := -1653947/1000000) 125 65
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t26 : ((1712479901717/10000000000000 : ℚ) : ℝ) ≤ stT125 26 := by
  have hc : ((873197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1712479901717/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((873197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c27 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((49177/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330211/1250000) (δ := 809/100000000) (ψ := -1653947/1000000) 125 66
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t27 : ((47315757/500000000 : ℚ) : ℝ) ≤ stT125 27 := by
  have hc : ((12293/25000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47315757/500000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((12293/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c28 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-940163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6984763/10000000) (δ := 1163/100000000) (ψ := -1653947/1000000) 125 67
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t28 : ((-1776836152299/10000000000000 : ℚ) : ℝ) ≤ stT125 28 := by
  have hc : ((-940213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1776836152299/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-940213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c29 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-1357/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159251/400000) (δ := 893/100000000) (ψ := -1653947/1000000) 125 67
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t29 : ((-10102758237/2500000000000 : ℚ) : ℝ) ≤ stT125 29 := by
  have hc : ((-10881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10102758237/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-10881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c30 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((449573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1132453/10000000) (δ := 51/5000000) (ψ := -1653947/1000000) 125 68
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t30 : ((205189553767/1250000000000 : ℚ) : ℝ) ≤ stT125 30 := by
  have hc : ((112387/125000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205189553767/1250000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((112387/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c31 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-13681/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6593597/10000000) (δ := 303/25000000) (ψ := -1653947/1000000) 125 69
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t31 : ((-393171487059/2500000000000 : ℚ) : ℝ) ≤ stT125 31 := by
  have hc : ((-437817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393171487059/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-437817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c32 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((237361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3327871/10000000) (δ := 621/50000000) (ψ := -1653947/1000000) 125 69
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t32 : ((209755158613/5000000000000 : ℚ) : ℝ) ≤ stT125 32 := by
  have hc : ((237311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209755158613/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((237311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c33 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((448617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2763949/10000000) (δ := 371/50000000) (ψ := -1653947/1000000) 125 70
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t33 : ((97606833499/1250000000000 : ℚ) : ℝ) ≤ stT125 33 := by
  have hc : ((448567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97606833499/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((448567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c34 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-870021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3282551/5000000) (δ := 971/100000000) (ψ := -1653947/1000000) 125 70
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t34 : ((-746079792003/5000000000000 : ℚ) : ℝ) ≤ stT125 34 := by
  have hc : ((-870071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-746079792003/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-870071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c35 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((124929/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2633/312500) (δ := 371/50000000) (ψ := -1653947/1000000) 125 71
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t35 : ((211157923707/1250000000000 : ℚ) : ℝ) ≤ stT125 35 := by
  have hc : ((499691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211157923707/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((499691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c36 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-188143/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349441/500000) (δ := 79/10000000) (ψ := -1653947/1000000) 125 72
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t36 : ((-313588396051/2000000000000 : ℚ) : ℝ) ≤ stT125 36 := by
  have hc : ((-188153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313588396051/2000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-188153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c37 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((404207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1573359/10000000) (δ := 113/10000000) (ψ := -1653947/1000000) 125 72
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t37 : ((332235380999/2500000000000 : ℚ) : ℝ) ≤ stT125 37 := by
  have hc : ((202091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332235380999/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((202091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c38 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-681283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5800777/10000000) (δ := 357/50000000) (ψ := -1653947/1000000) 125 73
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t38 : ((-221053722519/2000000000000 : ℚ) : ℝ) ≤ stT125 38 := by
  have hc : ((-681333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221053722519/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-681333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c39 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((75067/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2316563/10000000) (δ := 689/100000000) (ψ := -1653947/1000000) 125 73
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t39 : ((480773411283/5000000000000 : ℚ) : ℝ) ≤ stT125 39 := by
  have hc : ((300243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480773411283/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((300243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c40 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-581879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1095917/2000000) (δ := 27/4000000) (ψ := -1653947/1000000) 125 74
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t40 : ((-920110637131/10000000000000 : ℚ) : ℝ) ≤ stT125 40 := by
  have hc : ((-581929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-920110637131/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-581929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c41 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((15643/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279607/1250000) (δ := 163/20000000) (ψ := -1653947/1000000) 125 74
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t41 : ((97713198879/1000000000000 : ℚ) : ℝ) ≤ stT125 41 := by
  have hc : ((62567/100000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97713198879/1000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((62567/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c42 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-90143/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2970311/5000000) (δ := 257/25000000) (ψ := -1653947/1000000) 125 75
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t42 : ((-278206715649/2500000000000 : ℚ) : ℝ) ≤ stT125 42 := by
  have hc : ((-360597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278206715649/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-360597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c43 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((168911/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 706329/5000000) (δ := 539/50000000) (ψ := -1653947/1000000) 125 75
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t43 : ((51514298297/400000000000 : ℚ) : ℝ) ≤ stT125 43 := by
  have hc : ((168901/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51514298297/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((168901/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c44 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-239043/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7111081/10000000) (δ := 857/100000000) (ψ := -1653947/1000000) 125 76
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t44 : ((-720779584827/5000000000000 : ℚ) : ℝ) ≤ stT125 44 := by
  have hc : ((-478111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-720779584827/5000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-478111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c45 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((62461/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88313/10000000) (δ := 279/25000000) (ψ := -1653947/1000000) 125 76
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t45 : ((744853130393/5000000000000 : ℚ) : ℝ) ≤ stT125 45 := by
  have hc : ((499663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((744853130393/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((499663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c46 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-909151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1356019/2000000) (δ := 593/50000000) (ψ := -1653947/1000000) 125 76
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t46 : ((-67027206921/500000000000 : ℚ) : ℝ) ≤ stT125 46 := by
  have hc : ((-909201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67027206921/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-909201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c47 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((126987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2207179/10000000) (δ := 623/50000000) (ψ := -1653947/1000000) 125 77
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t47 : ((185214874073/2000000000000 : ℚ) : ℝ) ≤ stT125 47 := by
  have hc : ((126977/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185214874073/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((126977/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c48 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-177069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4372011/10000000) (δ := 573/50000000) (ψ := -1653947/1000000) 125 77
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t48 : ((-15978082109/625000000000 : ℚ) : ℝ) ≤ stT125 48 := by
  have hc : ((-177119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15978082109/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-177119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c49 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-376647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195697/400000) (δ := 599/50000000) (ψ := -1653947/1000000) 125 78
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t49 : ((-134534696671/2500000000000 : ℚ) : ℝ) ≤ stT125 49 := by
  have hc : ((-376697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134534696671/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-376697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c50 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((42139/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1420921/10000000) (δ := 243/20000000) (ψ := -1653947/1000000) 125 78
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t50 : ((119179972149/1000000000000 : ℚ) : ℝ) ≤ stT125 50 := by
  have hc : ((84273/100000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119179972149/1000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((84273/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c51 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-248803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3804621/5000000) (δ := 7/800000) (ψ := -1653947/1000000) 125 78
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t51 : ((-696823234311/5000000000000 : ℚ) : ℝ) ≤ stT125 51 := by
  have hc : ((-497631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-696823234311/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-497631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c52 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((687883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2030569/10000000) (δ := 207/20000000) (ψ := -1653947/1000000) 125 79
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t52 : ((3815409651/40000000000 : ℚ) : ℝ) ≤ stT125 52 := by
  have hc : ((687833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3815409651/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((687833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c53 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((1/500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490249/1250000) (δ := 219/20000000) (ψ := -1653947/1000000) 125 79
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t53 : ((10714119/40000000000 : ℚ) : ℝ) ≤ stT125 53 := by
  have hc : ((39/20000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10714119/40000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((39/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c54 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-180567/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148617/250000) (δ := 347/50000000) (ψ := -1653947/1000000) 125 80
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t54 : ((-122868819913/1250000000000 : ℚ) : ℝ) ≤ stT125 54 := by
  have hc : ((-361159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122868819913/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-361159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c55 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((199291/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105287/5000000) (δ := 1049/100000000) (ψ := -1653947/1000000) 125 80
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t55 : ((268710301119/2000000000000 : ℚ) : ℝ) ≤ stT125 55 := by
  have hc : ((199281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268710301119/2000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((199281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c56 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-562401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5420209/10000000) (δ := 1119/100000000) (ψ := -1653947/1000000) 125 80
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t56 : ((-751607208457/10000000000000 : ℚ) : ℝ) ≤ stT125 56 := by
  have hc : ((-562451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751607208457/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-562451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c57 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-325801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4756637/10000000) (δ := 81/10000000) (ψ := -1653947/1000000) 125 81
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t57 : ((-431600402583/10000000000000 : ℚ) : ℝ) ≤ stT125 57 := by
  have hc : ((-325851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431600402583/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-325851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c58 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((48171/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 678283/10000000) (δ := 1143/100000000) (ψ := -1653947/1000000) 125 81
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t58 : ((15812080821/125000000000 : ℚ) : ℝ) ≤ stT125 58 := by
  have hc : ((96337/100000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15812080821/125000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((96337/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c59 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-742853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3010147/5000000) (δ := 703/100000000) (ψ := -1653947/1000000) 125 81
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t59 : ((-96717798667/1000000000000 : ℚ) : ℝ) ≤ stT125 59 := by
  have hc : ((-742903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96717798667/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-742903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c60 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-100991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -887089/2000000) (δ := 77/10000000) (ψ := -1653947/1000000) 125 82
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t60 : ((-3260278773/125000000000 : ℚ) : ℝ) ≤ stT125 60 := by
  have hc : ((-12627/62500 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3260278773/125000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-12627/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c61 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((478837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 364981/5000000) (δ := 1/125000) (ψ := -1653947/1000000) 125 82
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t61 : ((9578993169/78125000000 : ℚ) : ℝ) ≤ stT125 61 := by
  have hc : ((119703/125000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9578993169/78125000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((119703/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c62 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-34219/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2905687/5000000) (δ := 103/10000000) (ψ := -1653947/1000000) 125 82
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t62 : ((-43461373443/500000000000 : ℚ) : ℝ) ≤ stT125 62 := by
  have hc : ((-68443/100000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43461373443/500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-68443/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c63 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-378149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2448241/5000000) (δ := 233/25000000) (ψ := -1653947/1000000) 125 83
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t63 : ((-238243056259/5000000000000 : ℚ) : ℝ) ≤ stT125 63 := by
  have hc : ((-378199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238243056259/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-378199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c64 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((19999/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24879/10000000) (δ := 1011/100000000) (ψ := -1653947/1000000) 125 83
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t64 : ((9999/80000 : ℚ) : ℝ) ≤ stT125 64 := by
  have hc : ((9999/10000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9999/80000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((9999/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c65 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-368299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2434969/5000000) (δ := 871/100000000) (ψ := -1653947/1000000) 125 83
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t65 : ((-114220236363/2500000000000 : ℚ) : ℝ) ≤ stT125 65 := by
  have hc : ((-368349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114220236363/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-368349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c66 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-377607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6066941/10000000) (δ := 761/100000000) (ψ := -1653947/1000000) 125 84
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t66 : ((-2905205583/31250000000 : ℚ) : ℝ) ≤ stT125 66 := by
  have hc : ((-11801/15625 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2905205583/31250000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-11801/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c67 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((854067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341901/2500000) (δ := 1031/100000000) (ψ := -1653947/1000000) 125 84
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t67 : ((521673722399/5000000000000 : ℚ) : ℝ) ≤ stT125 67 := by
  have hc : ((854017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((521673722399/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((854017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c68 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((65707/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326211/1000000) (δ := 1221/100000000) (ψ := -1653947/1000000) 125 84
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t68 : ((79666274871/2500000000000 : ℚ) : ℝ) ≤ stT125 68 := by
  have hc : ((131389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79666274871/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((131389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c69 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-999929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1564847/2000000) (δ := 1221/100000000) (ψ := -1653947/1000000) 125 84
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t69 : ((-1203833718961/10000000000000 : ℚ) : ℝ) ≤ stT125 69 := by
  have hc : ((-999979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1203833718961/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-999979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c70 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((13389/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211703/625000) (δ := 19/2500000) (ψ := -1653947/1000000) 125 85
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t70 : ((31998345209/1250000000000 : ℚ) : ℝ) ≤ stT125 70 := by
  have hc : ((107087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31998345209/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((107087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c71 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((913829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1045451/10000000) (δ := 953/100000000) (ψ := -1653947/1000000) 125 85
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t71 : ((1084455555399/10000000000000 : ℚ) : ℝ) ≤ stT125 71 := by
  have hc : ((913779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1084455555399/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((913779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c72 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-561059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5416151/10000000) (δ := 21/2000000) (ψ := -1653947/1000000) 125 85
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t72 : ((-41329605613/625000000000 : ℚ) : ℝ) ≤ stT125 72 := by
  have hc : ((-561109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41329605613/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-561109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c73 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-183087/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5981399/10000000) (δ := 77/10000000) (ψ := -1653947/1000000) 125 86
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t73 : ((-107150925997/1250000000000 : ℚ) : ℝ) ≤ stT125 73 := by
  have hc : ((-366199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107150925997/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-366199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c74 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((154013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54051/312500) (δ := 1163/100000000) (ψ := -1653947/1000000) 125 86
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t74 : ((44756197857/500000000000 : ℚ) : ℝ) ≤ stT125 74 := by
  have hc : ((154003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44756197857/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((154003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c75 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((552009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2465061/10000000) (δ := 7/625000) (ψ := -1653947/1000000) 125 86
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t75 : ((6373470573/100000000000 : ℚ) : ℝ) ≤ stT125 75 := by
  have hc : ((551959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6373470573/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((551959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c76 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-877623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1320839/2000000) (δ := 19/2500000) (ψ := -1653947/1000000) 125 86
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t76 : ((-1006760267167/10000000000000 : ℚ) : ℝ) ≤ stT125 76 := by
  have hc : ((-877673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1006760267167/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-877673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c77 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-52869/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5018743/10000000) (δ := 999/100000000) (ψ := -1653947/1000000) 125 87
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t77 : ((-120513904303/2500000000000 : ℚ) : ℝ) ≤ stT125 77 := by
  have hc : ((-211501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120513904303/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-211501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c78 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((923161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -986429/10000000) (δ := 939/100000000) (ψ := -1653947/1000000) 125 87
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t78 : ((1045217353747/10000000000000 : ℚ) : ℝ) ≤ stT125 78 := by
  have hc : ((923111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1045217353747/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((923111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c79 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((364401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2994517/10000000) (δ := 327/50000000) (ψ := -1653947/1000000) 125 87
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t79 : ((409926573537/10000000000000 : ℚ) : ℝ) ≤ stT125 79 := by
  have hc : ((364351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409926573537/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((364351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c80 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-465903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3462693/5000000) (δ := 839/100000000) (ψ := -1653947/1000000) 125 87
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t80 : ((-32557709097/312500000000 : ℚ) : ℝ) ≤ stT125 80 := by
  have hc : ((-58241/62500 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32557709097/312500000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-58241/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c81 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-94913/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245027/500000) (δ := 131/20000000) (ψ := -1653947/1000000) 125 88
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t81 : ((-26368215539/625000000000 : ℚ) : ℝ) ≤ stT125 81 := by
  have hc : ((-189851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26368215539/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-189851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c82 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((455219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133267/1250000) (δ := 43/6250000) (ψ := -1653947/1000000) 125 88
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t82 : ((50267756211/500000000000 : ℚ) : ℝ) ≤ stT125 82 := by
  have hc : ((227597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50267756211/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((227597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c83 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((57953/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2721789/10000000) (δ := 297/25000000) (ψ := -1653947/1000000) 125 88
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t83 : ((127209573127/2500000000000 : ℚ) : ℝ) ≤ stT125 83 := by
  have hc : ((231787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127209573127/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((231787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c84 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-849451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6464349/10000000) (δ := 161/12500000) (ψ := -1653947/1000000) 125 88
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t84 : ((-92688204609/1000000000000 : ℚ) : ℝ) ≤ stT125 84 := by
  have hc : ((-849501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92688204609/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-849501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c85 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-150767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2772673/5000000) (δ := 139/20000000) (ψ := -1653947/1000000) 125 89
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t85 : ((-327086874027/5000000000000 : ℚ) : ℝ) ≤ stT125 85 := by
  have hc : ((-301559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327086874027/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-301559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c86 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((363747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -945167/5000000) (δ := 47/4000000) (ψ := -1653947/1000000) 125 89
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t86 : ((196105626547/2500000000000 : ℚ) : ℝ) ≤ stT125 86 := by
  have hc : ((181861/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196105626547/2500000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((181861/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c87 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((385951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1722423/10000000) (δ := 131/12500000) (ψ := -1653947/1000000) 125 89
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t87 : ((12929871741/156250000000 : ℚ) : ℝ) ≤ stT125 87 := by
  have hc : ((192963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12929871741/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((192963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c88 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-259961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5293891/10000000) (δ := 539/50000000) (ψ := -1653947/1000000) 125 89
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t88 : ((-34643264493/625000000000 : ℚ) : ℝ) ≤ stT125 88 := by
  have hc : ((-129993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34643264493/625000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-129993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c89 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-925513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3441481/5000000) (δ := 209/25000000) (ψ := -1653947/1000000) 125 90
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t89 : ((-490547464437/5000000000000 : ℚ) : ℝ) ≤ stT125 89 := by
  have hc : ((-925563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490547464437/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-925563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c90 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((106319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -678261/2000000) (δ := 433/50000000) (ψ := -1653947/1000000) 125 90
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t90 : ((14005456881/625000000000 : ℚ) : ℝ) ≤ stT125 90 := by
  have hc : ((53147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14005456881/625000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((53147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c91 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((199939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61769/10000000) (δ := 663/50000000) (ψ := -1653947/1000000) 125 90
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t91 : ((52395592959/500000000000 : ℚ) : ℝ) ≤ stT125 91 := by
  have hc : ((199929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52395592959/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((199929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c92 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((35797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3477103/10000000) (δ := 117/12500000) (ψ := -1653947/1000000) 125 90
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t92 : ((9327631041/500000000000 : ℚ) : ℝ) ≤ stT125 92 := by
  have hc : ((35787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9327631041/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((35787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c93 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-9213/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3427757/5000000) (δ := 563/50000000) (ψ := -1653947/1000000) 125 90
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t93 : ((-2388489313/25000000000 : ℚ) : ℝ) ≤ stT125 93 := by
  have hc : ((-18427/20000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2388489313/25000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-18427/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c94 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-295893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5510171/10000000) (δ := 1007/100000000) (ψ := -1653947/1000000) 125 91
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t94 : ((-76304083849/1250000000000 : ℚ) : ℝ) ≤ stT125 94 := by
  have hc : ((-147959/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76304083849/1250000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-147959/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c95 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((127229/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1101631/5000000) (δ := 1117/100000000) (ψ := -1653947/1000000) 125 91
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t95 : ((65261947591/1000000000000 : ℚ) : ℝ) ≤ stT125 95 := by
  have hc : ((127219/200000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65261947591/1000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((127219/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c96 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((22749/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1069019/10000000) (δ := 1107/100000000) (ψ := -1653947/1000000) 125 91
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t96 : ((4643361721/50000000000 : ℚ) : ℝ) ≤ stT125 96 := by
  have hc : ((90991/100000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4643361721/50000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((90991/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c97 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-151573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 430739/1000000) (δ := 947/100000000) (ψ := -1653947/1000000) 125 91
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t97 : ((-153949958181/10000000000000 : ℚ) : ℝ) ≤ stT125 97 := by
  have hc : ((-151623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153949958181/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-151623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c98 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-30959/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7512547/10000000) (δ := 977/100000000) (ψ := -1653947/1000000) 125 91
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t98 : ((-500398481457/5000000000000 : ℚ) : ℝ) ≤ stT125 98 := by
  have hc : ((-495369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500398481457/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-495369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c99 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((-212211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12557/25000) (δ := 157/25000000) (ψ := -1653947/1000000) 125 92
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t99 : ((-26663155621/625000000000 : ℚ) : ℝ) ≤ stT125 99 := by
  have hc : ((-53059/125000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26663155621/625000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-53059/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_c100 :
    |Real.cos (((125 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ))
      - ((364879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1882071/10000000) (δ := 519/50000000) (ψ := -1653947/1000000) 125 92
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st125_t100 : ((182426817573/2500000000000 : ℚ) : ℝ) ≤ stT125 100 := by
  have hc : ((182427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((125 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1653947/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st125_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182426817573/2500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((182427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st125_p1 : ((-166210016621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT125 (i+1) := by
  rw [Finset.sum_range_one]
  exact st125_t1

theorem st125_p2 : ((5851801196461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT125 (i+1))
      = (∑ i ∈ Finset.range 1, stT125 (i+1)) + stT125 2 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 1
    simpa using h
  have hprev := st125_p1
  have hstep := st125_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p3 : ((2014864233237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT125 (i+1))
      = (∑ i ∈ Finset.range 2, stT125 (i+1)) + stT125 3 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 2
    simpa using h
  have hprev := st125_p2
  have hstep := st125_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p4 : ((2564802233237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT125 (i+1))
      = (∑ i ∈ Finset.range 3, stT125 (i+1)) + stT125 4 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 3
    simpa using h
  have hprev := st125_p3
  have hstep := st125_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p5 : ((477244179697/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT125 (i+1))
      = (∑ i ∈ Finset.range 4, stT125 (i+1)) + stT125 5 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 4
    simpa using h
  have hprev := st125_p4
  have hstep := st125_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p6 : ((15366202826793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT125 (i+1))
      = (∑ i ∈ Finset.range 5, stT125 (i+1)) + stT125 6 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 5
    simpa using h
  have hprev := st125_p5
  have hstep := st125_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p7 : ((19102358242929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT125 (i+1))
      = (∑ i ∈ Finset.range 6, stT125 (i+1)) + stT125 7 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 6
    simpa using h
  have hprev := st125_p6
  have hstep := st125_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p8 : ((3344245118281/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT125 (i+1))
      = (∑ i ∈ Finset.range 7, stT125 (i+1)) + stT125 8 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 7
    simpa using h
  have hprev := st125_p7
  have hstep := st125_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p9 : ((20015385261989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT125 (i+1))
      = (∑ i ∈ Finset.range 8, stT125 (i+1)) + stT125 9 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 8
    simpa using h
  have hprev := st125_p8
  have hstep := st125_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p10 : ((22861921552647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT125 (i+1))
      = (∑ i ∈ Finset.range 9, stT125 (i+1)) + stT125 10 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 9
    simpa using h
  have hprev := st125_p9
  have hstep := st125_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p11 : ((3226944172933/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT125 (i+1))
      = (∑ i ∈ Finset.range 10, stT125 (i+1)) + stT125 11 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 10
    simpa using h
  have hprev := st125_p10
  have hstep := st125_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p12 : ((622601752493/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT125 (i+1))
      = (∑ i ∈ Finset.range 11, stT125 (i+1)) + stT125 12 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 11
    simpa using h
  have hprev := st125_p11
  have hstep := st125_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p13 : ((24192608849699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT125 (i+1))
      = (∑ i ∈ Finset.range 12, stT125 (i+1)) + stT125 13 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 12
    simpa using h
  have hprev := st125_p12
  have hstep := st125_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p14 : ((24454206784871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT125 (i+1))
      = (∑ i ∈ Finset.range 13, stT125 (i+1)) + stT125 14 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 13
    simpa using h
  have hprev := st125_p13
  have hstep := st125_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p15 : ((26122532511191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT125 (i+1))
      = (∑ i ∈ Finset.range 14, stT125 (i+1)) + stT125 15 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 14
    simpa using h
  have hprev := st125_p14
  have hstep := st125_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p16 : ((11957844564227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT125 (i+1))
      = (∑ i ∈ Finset.range 15, stT125 (i+1)) + stT125 16 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 15
    simpa using h
  have hprev := st125_p15
  have hstep := st125_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p17 : ((11117827017991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT125 (i+1))
      = (∑ i ∈ Finset.range 16, stT125 (i+1)) + stT125 17 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 16
    simpa using h
  have hprev := st125_p16
  have hstep := st125_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p18 : ((11231277557917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT125 (i+1))
      = (∑ i ∈ Finset.range 17, stT125 (i+1)) + stT125 18 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 17
    simpa using h
  have hprev := st125_p17
  have hstep := st125_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p19 : ((592592236613/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT125 (i+1))
      = (∑ i ∈ Finset.range 18, stT125 (i+1)) + stT125 19 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 18
    simpa using h
  have hprev := st125_p18
  have hstep := st125_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p20 : ((25144362835883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT125 (i+1))
      = (∑ i ∈ Finset.range 19, stT125 (i+1)) + stT125 20 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 19
    simpa using h
  have hprev := st125_p19
  have hstep := st125_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p21 : ((26220464637379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT125 (i+1))
      = (∑ i ∈ Finset.range 20, stT125 (i+1)) + stT125 21 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 20
    simpa using h
  have hprev := st125_p20
  have hstep := st125_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p22 : ((2632172004583/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT125 (i+1))
      = (∑ i ∈ Finset.range 21, stT125 (i+1)) + stT125 22 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 21
    simpa using h
  have hprev := st125_p21
  have hstep := st125_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p23 : ((5002372646801/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT125 (i+1))
      = (∑ i ∈ Finset.range 22, stT125 (i+1)) + stT125 23 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 22
    simpa using h
  have hprev := st125_p22
  have hstep := st125_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p24 : ((22975748833909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT125 (i+1))
      = (∑ i ∈ Finset.range 23, stT125 (i+1)) + stT125 24 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 23
    simpa using h
  have hprev := st125_p23
  have hstep := st125_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p25 : ((22348852520461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT125 (i+1))
      = (∑ i ∈ Finset.range 24, stT125 (i+1)) + stT125 25 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 24
    simpa using h
  have hprev := st125_p24
  have hstep := st125_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p26 : ((12030666211089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT125 (i+1))
      = (∑ i ∈ Finset.range 25, stT125 (i+1)) + stT125 26 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 25
    simpa using h
  have hprev := st125_p25
  have hstep := st125_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p27 : ((12503823781089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT125 (i+1))
      = (∑ i ∈ Finset.range 26, stT125 (i+1)) + stT125 27 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 26
    simpa using h
  have hprev := st125_p26
  have hstep := st125_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p28 : ((23230811409879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT125 (i+1))
      = (∑ i ∈ Finset.range 27, stT125 (i+1)) + stT125 28 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 27
    simpa using h
  have hprev := st125_p27
  have hstep := st125_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p29 : ((23190400376931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT125 (i+1))
      = (∑ i ∈ Finset.range 28, stT125 (i+1)) + stT125 29 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 28
    simpa using h
  have hprev := st125_p28
  have hstep := st125_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p30 : ((24831916807067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT125 (i+1))
      = (∑ i ∈ Finset.range 29, stT125 (i+1)) + stT125 30 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 29
    simpa using h
  have hprev := st125_p29
  have hstep := st125_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p31 : ((23259230858831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT125 (i+1))
      = (∑ i ∈ Finset.range 30, stT125 (i+1)) + stT125 31 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 30
    simpa using h
  have hprev := st125_p30
  have hstep := st125_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p32 : ((23678741176057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT125 (i+1))
      = (∑ i ∈ Finset.range 31, stT125 (i+1)) + stT125 32 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 31
    simpa using h
  have hprev := st125_p31
  have hstep := st125_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p33 : ((24459595844049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT125 (i+1))
      = (∑ i ∈ Finset.range 32, stT125 (i+1)) + stT125 33 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 32
    simpa using h
  have hprev := st125_p32
  have hstep := st125_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p34 : ((22967436260043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT125 (i+1))
      = (∑ i ∈ Finset.range 33, stT125 (i+1)) + stT125 34 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 33
    simpa using h
  have hprev := st125_p33
  have hstep := st125_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p35 : ((24656699649699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT125 (i+1))
      = (∑ i ∈ Finset.range 34, stT125 (i+1)) + stT125 35 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 34
    simpa using h
  have hprev := st125_p34
  have hstep := st125_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p36 : ((5772189417361/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT125 (i+1))
      = (∑ i ∈ Finset.range 35, stT125 (i+1)) + stT125 36 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 35
    simpa using h
  have hprev := st125_p35
  have hstep := st125_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p37 : ((152610619959/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT125 (i+1))
      = (∑ i ∈ Finset.range 36, stT125 (i+1)) + stT125 37 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 36
    simpa using h
  have hprev := st125_p36
  have hstep := st125_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p38 : ((4662486116169/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT125 (i+1))
      = (∑ i ∈ Finset.range 37, stT125 (i+1)) + stT125 38 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 37
    simpa using h
  have hprev := st125_p37
  have hstep := st125_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p39 : ((24273977403411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT125 (i+1))
      = (∑ i ∈ Finset.range 38, stT125 (i+1)) + stT125 39 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 38
    simpa using h
  have hprev := st125_p38
  have hstep := st125_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p40 : ((583846669157/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT125 (i+1))
      = (∑ i ∈ Finset.range 39, stT125 (i+1)) + stT125 40 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 39
    simpa using h
  have hprev := st125_p39
  have hstep := st125_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p41 : ((2433099875507/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT125 (i+1))
      = (∑ i ∈ Finset.range 40, stT125 (i+1)) + stT125 41 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 40
    simpa using h
  have hprev := st125_p40
  have hstep := st125_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p42 : ((11609085946237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT125 (i+1))
      = (∑ i ∈ Finset.range 41, stT125 (i+1)) + stT125 42 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 41
    simpa using h
  have hprev := st125_p41
  have hstep := st125_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p43 : ((24506029349899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT125 (i+1))
      = (∑ i ∈ Finset.range 42, stT125 (i+1)) + stT125 43 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 42
    simpa using h
  have hprev := st125_p42
  have hstep := st125_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p44 : ((4612894036049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT125 (i+1))
      = (∑ i ∈ Finset.range 43, stT125 (i+1)) + stT125 44 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 43
    simpa using h
  have hprev := st125_p43
  have hstep := st125_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p45 : ((24554176441031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT125 (i+1))
      = (∑ i ∈ Finset.range 44, stT125 (i+1)) + stT125 45 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 44
    simpa using h
  have hprev := st125_p44
  have hstep := st125_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p46 : ((23213632302611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT125 (i+1))
      = (∑ i ∈ Finset.range 45, stT125 (i+1)) + stT125 46 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 45
    simpa using h
  have hprev := st125_p45
  have hstep := st125_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p47 : ((1508731667061/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT125 (i+1))
      = (∑ i ∈ Finset.range 46, stT125 (i+1)) + stT125 47 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 46
    simpa using h
  have hprev := st125_p46
  have hstep := st125_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p48 : ((186594198119/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT125 (i+1))
      = (∑ i ∈ Finset.range 47, stT125 (i+1)) + stT125 48 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 47
    simpa using h
  have hprev := st125_p47
  have hstep := st125_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p49 : ((5836479643137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT125 (i+1))
      = (∑ i ∈ Finset.range 48, stT125 (i+1)) + stT125 49 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 48
    simpa using h
  have hprev := st125_p48
  have hstep := st125_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p50 : ((12268859147019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT125 (i+1))
      = (∑ i ∈ Finset.range 49, stT125 (i+1)) + stT125 50 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 49
    simpa using h
  have hprev := st125_p49
  have hstep := st125_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p51 : ((2893008978177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT125 (i+1))
      = (∑ i ∈ Finset.range 50, stT125 (i+1)) + stT125 51 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 50
    simpa using h
  have hprev := st125_p50
  have hstep := st125_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p52 : ((12048962119083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT125 (i+1))
      = (∑ i ∈ Finset.range 51, stT125 (i+1)) + stT125 52 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 51
    simpa using h
  have hprev := st125_p51
  have hstep := st125_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p53 : ((6025150691979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT125 (i+1))
      = (∑ i ∈ Finset.range 52, stT125 (i+1)) + stT125 53 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 52
    simpa using h
  have hprev := st125_p52
  have hstep := st125_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p54 : ((5779413052153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT125 (i+1))
      = (∑ i ∈ Finset.range 53, stT125 (i+1)) + stT125 54 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 53
    simpa using h
  have hprev := st125_p53
  have hstep := st125_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p55 : ((24461203714207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT125 (i+1))
      = (∑ i ∈ Finset.range 54, stT125 (i+1)) + stT125 55 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 54
    simpa using h
  have hprev := st125_p54
  have hstep := st125_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p56 : ((94838386023/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT125 (i+1))
      = (∑ i ∈ Finset.range 55, stT125 (i+1)) + stT125 56 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 55
    simpa using h
  have hprev := st125_p55
  have hstep := st125_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p57 : ((23277996103167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT125 (i+1))
      = (∑ i ∈ Finset.range 56, stT125 (i+1)) + stT125 57 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 56
    simpa using h
  have hprev := st125_p56
  have hstep := st125_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p58 : ((24542962568847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT125 (i+1))
      = (∑ i ∈ Finset.range 57, stT125 (i+1)) + stT125 58 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 57
    simpa using h
  have hprev := st125_p57
  have hstep := st125_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p59 : ((23575784582177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT125 (i+1))
      = (∑ i ∈ Finset.range 58, stT125 (i+1)) + stT125 59 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 58
    simpa using h
  have hprev := st125_p58
  have hstep := st125_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p60 : ((23314962280337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT125 (i+1))
      = (∑ i ∈ Finset.range 59, stT125 (i+1)) + stT125 60 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 59
    simpa using h
  have hprev := st125_p59
  have hstep := st125_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p61 : ((24541073405969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT125 (i+1))
      = (∑ i ∈ Finset.range 60, stT125 (i+1)) + stT125 61 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 60
    simpa using h
  have hprev := st125_p60
  have hstep := st125_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p62 : ((23671845937109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT125 (i+1))
      = (∑ i ∈ Finset.range 61, stT125 (i+1)) + stT125 62 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 61
    simpa using h
  have hprev := st125_p61
  have hstep := st125_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p63 : ((23195359824591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT125 (i+1))
      = (∑ i ∈ Finset.range 62, stT125 (i+1)) + stT125 63 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 62
    simpa using h
  have hprev := st125_p62
  have hstep := st125_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p64 : ((24445234824591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT125 (i+1))
      = (∑ i ∈ Finset.range 63, stT125 (i+1)) + stT125 64 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 63
    simpa using h
  have hprev := st125_p63
  have hstep := st125_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p65 : ((23988353879139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT125 (i+1))
      = (∑ i ∈ Finset.range 64, stT125 (i+1)) + stT125 65 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 64
    simpa using h
  have hprev := st125_p64
  have hstep := st125_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p66 : ((23058688092579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT125 (i+1))
      = (∑ i ∈ Finset.range 65, stT125 (i+1)) + stT125 66 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 65
    simpa using h
  have hprev := st125_p65
  have hstep := st125_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p67 : ((24102035537377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT125 (i+1))
      = (∑ i ∈ Finset.range 66, stT125 (i+1)) + stT125 67 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 66
    simpa using h
  have hprev := st125_p66
  have hstep := st125_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p68 : ((24420700636861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT125 (i+1))
      = (∑ i ∈ Finset.range 67, stT125 (i+1)) + stT125 68 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 67
    simpa using h
  have hprev := st125_p67
  have hstep := st125_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p69 : ((232168669179/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT125 (i+1))
      = (∑ i ∈ Finset.range 68, stT125 (i+1)) + stT125 69 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 68
    simpa using h
  have hprev := st125_p68
  have hstep := st125_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p70 : ((5868213419893/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT125 (i+1))
      = (∑ i ∈ Finset.range 69, stT125 (i+1)) + stT125 70 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 69
    simpa using h
  have hprev := st125_p69
  have hstep := st125_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p71 : ((24557309234971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT125 (i+1))
      = (∑ i ∈ Finset.range 70, stT125 (i+1)) + stT125 71 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 70
    simpa using h
  have hprev := st125_p70
  have hstep := st125_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p72 : ((23896035545163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT125 (i+1))
      = (∑ i ∈ Finset.range 71, stT125 (i+1)) + stT125 72 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 71
    simpa using h
  have hprev := st125_p71
  have hstep := st125_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p73 : ((23038828137187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT125 (i+1))
      = (∑ i ∈ Finset.range 72, stT125 (i+1)) + stT125 73 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 72
    simpa using h
  have hprev := st125_p72
  have hstep := st125_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p74 : ((23933952094327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT125 (i+1))
      = (∑ i ∈ Finset.range 73, stT125 (i+1)) + stT125 74 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 73
    simpa using h
  have hprev := st125_p73
  have hstep := st125_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p75 : ((24571299151627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT125 (i+1))
      = (∑ i ∈ Finset.range 74, stT125 (i+1)) + stT125 75 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 74
    simpa using h
  have hprev := st125_p74
  have hstep := st125_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p76 : ((1178226944223/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT125 (i+1))
      = (∑ i ∈ Finset.range 75, stT125 (i+1)) + stT125 76 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 75
    simpa using h
  have hprev := st125_p75
  have hstep := st125_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p77 : ((1442655204203/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT125 (i+1))
      = (∑ i ∈ Finset.range 76, stT125 (i+1)) + stT125 77 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 76
    simpa using h
  have hprev := st125_p76
  have hstep := st125_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p78 : ((4825540124199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT125 (i+1))
      = (∑ i ∈ Finset.range 77, stT125 (i+1)) + stT125 78 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 77
    simpa using h
  have hprev := st125_p77
  have hstep := st125_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p79 : ((6134406798633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT125 (i+1))
      = (∑ i ∈ Finset.range 78, stT125 (i+1)) + stT125 79 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 78
    simpa using h
  have hprev := st125_p78
  have hstep := st125_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p80 : ((5873945125857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT125 (i+1))
      = (∑ i ∈ Finset.range 79, stT125 (i+1)) + stT125 80 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 79
    simpa using h
  have hprev := st125_p79
  have hstep := st125_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p81 : ((5768472263701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT125 (i+1))
      = (∑ i ∈ Finset.range 80, stT125 (i+1)) + stT125 81 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 80
    simpa using h
  have hprev := st125_p80
  have hstep := st125_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p82 : ((1504952761189/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT125 (i+1))
      = (∑ i ∈ Finset.range 81, stT125 (i+1)) + stT125 82 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 81
    simpa using h
  have hprev := st125_p81
  have hstep := st125_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p83 : ((6147020617883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT125 (i+1))
      = (∑ i ∈ Finset.range 82, stT125 (i+1)) + stT125 83 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 82
    simpa using h
  have hprev := st125_p82
  have hstep := st125_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p84 : ((11830600212721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT125 (i+1))
      = (∑ i ∈ Finset.range 83, stT125 (i+1)) + stT125 84 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 83
    simpa using h
  have hprev := st125_p83
  have hstep := st125_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p85 : ((5751756669347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT125 (i+1))
      = (∑ i ∈ Finset.range 84, stT125 (i+1)) + stT125 85 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 84
    simpa using h
  have hprev := st125_p84
  have hstep := st125_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p86 : ((2973931147947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT125 (i+1))
      = (∑ i ∈ Finset.range 85, stT125 (i+1)) + stT125 86 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 85
    simpa using h
  have hprev := st125_p85
  have hstep := st125_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p87 : ((984758439/400000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT125 (i+1))
      = (∑ i ∈ Finset.range 86, stT125 (i+1)) + stT125 87 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 86
    simpa using h
  have hprev := st125_p86
  have hstep := st125_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p88 : ((3008083592889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT125 (i+1))
      = (∑ i ∈ Finset.range 87, stT125 (i+1)) + stT125 88 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 87
    simpa using h
  have hprev := st125_p87
  have hstep := st125_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p89 : ((11541786907119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT125 (i+1))
      = (∑ i ∈ Finset.range 88, stT125 (i+1)) + stT125 89 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 88
    simpa using h
  have hprev := st125_p88
  have hstep := st125_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p90 : ((11653830562167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT125 (i+1))
      = (∑ i ∈ Finset.range 89, stT125 (i+1)) + stT125 90 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 89
    simpa using h
  have hprev := st125_p89
  have hstep := st125_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p91 : ((12177786491757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT125 (i+1))
      = (∑ i ∈ Finset.range 90, stT125 (i+1)) + stT125 91 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 90
    simpa using h
  have hprev := st125_p90
  have hstep := st125_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p92 : ((12271062802167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT125 (i+1))
      = (∑ i ∈ Finset.range 91, stT125 (i+1)) + stT125 92 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 91
    simpa using h
  have hprev := st125_p91
  have hstep := st125_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p93 : ((11793364939567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT125 (i+1))
      = (∑ i ∈ Finset.range 92, stT125 (i+1)) + stT125 93 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 92
    simpa using h
  have hprev := st125_p92
  have hstep := st125_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p94 : ((11488148604171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT125 (i+1))
      = (∑ i ∈ Finset.range 93, stT125 (i+1)) + stT125 94 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 93
    simpa using h
  have hprev := st125_p93
  have hstep := st125_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p95 : ((5907229171063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT125 (i+1))
      = (∑ i ∈ Finset.range 94, stT125 (i+1)) + stT125 95 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 94
    simpa using h
  have hprev := st125_p94
  have hstep := st125_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p96 : ((6139397257113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT125 (i+1))
      = (∑ i ∈ Finset.range 95, stT125 (i+1)) + stT125 96 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 95
    simpa using h
  have hprev := st125_p95
  have hstep := st125_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p97 : ((24403639070271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT125 (i+1))
      = (∑ i ∈ Finset.range 96, stT125 (i+1)) + stT125 97 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 96
    simpa using h
  have hprev := st125_p96
  have hstep := st125_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p98 : ((23402842107357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT125 (i+1))
      = (∑ i ∈ Finset.range 97, stT125 (i+1)) + stT125 98 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 97
    simpa using h
  have hprev := st125_p97
  have hstep := st125_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p99 : ((22976231617421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT125 (i+1))
      = (∑ i ∈ Finset.range 98, stT125 (i+1)) + stT125 99 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 98
    simpa using h
  have hprev := st125_p98
  have hstep := st125_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st125_p100 : ((23705938887713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT125 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT125 (i+1))
      = (∑ i ∈ Finset.range 99, stT125 (i+1)) + stT125 100 := by
    have h := Finset.sum_range_succ (fun i => stT125 (i+1)) 99
    simpa using h
  have hprev := st125_p99
  have hstep := st125_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 125`.** -/
theorem station_125_sign : 0 < hardyG (((125:ℕ)):ℝ) := by
  have hcore := phase_station_lower 125 100 (by norm_num) (by norm_num)
    ((-1653947/1000000 : ℚ) : ℝ)
  have hchain := st125_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT125 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((125:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-1653947/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((125:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((125:ℕ)):ℝ)+1) * ((((125:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((593401/400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((23705938887713/10000000000000 : ℚ) : ℝ) - ((593401/400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-1653947/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((125:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-1653947/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((125:ℕ)):ℝ))).re
      - Real.sin ((-1653947/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((125:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((125:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((125:ℕ)):ℝ)
      = ((((125:ℕ)):ℝ) * (Real.log (((125:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((125:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_125
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
  have hθwin : |(((-1653947/1000000 : ℚ) : ℝ) + ((20:ℤ)) * (2*Real.pi)) - theta (((125:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((125:ℕ)):ℝ))
    (φ := ((-1653947/1000000 : ℚ) : ℝ) + ((20:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-1653947/1000000 : ℚ)) : ℝ) 20).1,
    (cos_sin_shift (((-1653947/1000000 : ℚ)) : ℝ) 20).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_125_sign
end AxiomAudit
