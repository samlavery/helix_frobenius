import RequestProject.DVPSqrtTable

/-!
# Station `t = 62` of the extended Hardy ladder (sign -; rung-63)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT62 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((62 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))

theorem st62_c1 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((75003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3165227/10000000) (δ := 21/100000000) (ψ := -1266091/1000000) 62 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t1 : ((149981/500000 : ℚ) : ℝ) ≤ stT62 1 := by
  have hc : ((149981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149981/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((149981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c2 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((966667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 647297/10000000) (δ := 477/100000000) (ψ := -1266091/1000000) 62 7
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t2 : ((6835013570339/10000000000000 : ℚ) : ℝ) ≤ stT62 2 := by
  have hc : ((966617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6835013570339/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((966617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c3 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((965089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82817/1250000) (δ := 539/100000000) (ψ := -1266091/1000000) 62 11
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t3 : ((2785827298289/5000000000000 : ℚ) : ℝ) ≤ stT62 3 := by
  have hc : ((965039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2785827298289/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((965039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c4 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((366439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1870633/10000000) (δ := 11/3125000) (ψ := -1266091/1000000) 62 14
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t4 : ((183207/500000 : ℚ) : ℝ) ≤ stT62 4 := by
  have hc : ((183207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183207/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((183207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c5 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((433841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1300691/10000000) (δ := 57/10000000) (ψ := -1266091/1000000) 62 16
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t5 : ((48502092929/125000000000 : ℚ) : ℝ) ≤ stT62 5 := by
  have hc : ((54227/62500 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48502092929/125000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((54227/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c6 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((184253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -927697/5000000) (δ := 207/50000000) (ψ := -1266091/1000000) 62 18
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t6 : ((752158524921/2500000000000 : ℚ) : ℝ) ≤ stT62 6 := by
  have hc : ((368481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((752158524921/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((368481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c7 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-819881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3164999/5000000) (δ := 169/50000000) (ψ := -1266091/1000000) 62 19
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t7 : ((-619809620899/2000000000000 : ℚ) : ℝ) ≤ stT62 7 := by
  have hc : ((-819931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619809620899/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-819931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c8 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-91791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4388563/10000000) (δ := 99/25000000) (ψ := -1266091/1000000) 62 21
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t8 : ((-20288661859/312500000000 : ℚ) : ℝ) ≤ stT62 8 := by
  have hc : ((-11477/62500 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20288661859/312500000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-11477/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c9 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((370559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368031/2000000) (δ := 477/100000000) (ψ := -1266091/1000000) 62 22
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t9 : ((617556604911/2500000000000 : ℚ) : ℝ) ≤ stT62 9 := by
  have hc : ((185267/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((617556604911/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((185267/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c10 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((88379/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1217239/10000000) (δ := 137/25000000) (ψ := -1266091/1000000) 62 23
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t10 : ((139731533799/500000000000 : ℚ) : ℝ) ≤ stT62 10 := by
  have hc : ((44187/50000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139731533799/500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((44187/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c11 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((651793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -538031/2500000) (δ := 439/100000000) (ψ := -1266091/1000000) 62 24
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t11 : ((1965078791959/10000000000000 : ℚ) : ℝ) ≤ stT62 11 := by
  have hc : ((651743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1965078791959/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((651743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c12 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-88793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1093331/2500000) (δ := 167/50000000) (ψ := -1266091/1000000) 62 25
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t12 : ((-4006180299/78125000000 : ℚ) : ℝ) ≤ stT62 12 := by
  have hc : ((-44409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4006180299/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-44409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c13 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-997429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1918667/2500000) (δ := 1/312500) (ψ := -1266091/1000000) 62 26
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t13 : ((-2766509003979/10000000000000 : ℚ) : ℝ) ≤ stT62 13 := by
  have hc : ((-997479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2766509003979/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-997479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c14 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((45953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953017/2500000) (δ := 463/100000000) (ψ := -1266091/1000000) 62 26
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t14 : ((30670227159/2500000000000 : ℚ) : ℝ) ≤ stT62 14 := by
  have hc : ((45903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30670227159/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((45903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c15 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((7093/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601/5000) (δ := 79/12500000) (ψ := -1266091/1000000) 62 27
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t15 : ((22891260111/100000000000 : ℚ) : ℝ) ≤ stT62 15 := by
  have hc : ((35463/40000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22891260111/100000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((35463/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c16 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-929037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6906493/10000000) (δ := 521/100000000) (ψ := -1266091/1000000) 62 28
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t16 : ((-2322718429087/10000000000000 : ℚ) : ℝ) ≤ stT62 16 := by
  have hc : ((-929087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2322718429087/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-929087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c17 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((108711/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622581/2500000) (δ := 361/100000000) (ψ := -1266091/1000000) 62 28
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t17 : ((65909655639/500000000000 : ℚ) : ℝ) ≤ stT62 17 := by
  have hc : ((108701/200000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65909655639/500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((108701/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c18 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-2681/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -871617/2000000) (δ := 11/3125000) (ψ := -1266091/1000000) 62 29
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t18 : ((-202272642791/5000000000000 : ℚ) : ℝ) ≤ stT62 18 := by
  have hc : ((-85817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202272642791/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-85817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c19 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-2383/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2011167/5000000) (δ := 59/12500000) (ψ := -1266091/1000000) 62 29
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t19 : ((-21896591031/2500000000000 : ℚ) : ℝ) ≤ stT62 19 := by
  have hc : ((-19089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21896591031/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-19089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c20 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((76653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3735169/10000000) (δ := 423/100000000) (ψ := -1266091/1000000) 62 30
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t20 : ((171289440401/10000000000000 : ℚ) : ℝ) ≤ stT62 20 := by
  have hc : ((76603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171289440401/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((76603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c21 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((39863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3827307/10000000) (δ := 1/250000) (ψ := -1266091/1000000) 62 30
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t21 : ((43439526357/5000000000000 : ℚ) : ℝ) ≤ stT62 21 := by
  have hc : ((39813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43439526357/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((39813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c22 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-73217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2335027/5000000) (δ := 157/50000000) (ψ := -1266091/1000000) 62 31
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t22 : ((-39031469959/625000000000 : ℚ) : ℝ) ≤ stT62 22 := by
  have hc : ((-146459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39031469959/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-146459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c23 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((25239/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2219969/10000000) (δ := 549/100000000) (ψ := -1266091/1000000) 62 31
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t23 : ((6577847391/50000000000 : ℚ) : ℝ) ≤ stT62 23 := by
  have hc : ((25237/40000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6577847391/50000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((25237/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c24 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-231691/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3445627/5000000) (δ := 459/100000000) (ψ := -1266091/1000000) 62 32
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t24 : ((-472962915747/2500000000000 : ℚ) : ℝ) ≤ stT62 24 := by
  have hc : ((-463407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472962915747/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-463407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c25 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((487337/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112769/2000000) (δ := 499/100000000) (ψ := -1266091/1000000) 62 32
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t25 : ((30457/156250 : ℚ) : ℝ) ≤ stT62 25 := by
  have hc : ((30457/31250 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30457/156250 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((30457/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c26 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-593459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2757683/5000000) (δ := 399/100000000) (ψ := -1266091/1000000) 62 32
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t26 : ((-581983648729/5000000000000 : ℚ) : ℝ) ≤ stT62 26 := by
  have hc : ((-593509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-581983648729/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-593509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c27 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-20697/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4342847/10000000) (δ := 3/800000) (ψ := -1266091/1000000) 62 33
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t27 : ((-159373701313/5000000000000 : ℚ) : ℝ) ≤ stT62 27 := by
  have hc : ((-82813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159373701313/5000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-82813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c28 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((434491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 647069/5000000) (δ := 147/25000000) (ψ := -1266091/1000000) 62 33
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t28 : ((205265851263/1250000000000 : ℚ) : ℝ) ≤ stT62 28 := by
  have hc : ((217233/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205265851263/1250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((217233/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c29 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-225299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6733293/10000000) (δ := 7/1562500) (ψ := -1266091/1000000) 62 33
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t29 : ((-418393091171/2500000000000 : ℚ) : ℝ) ≤ stT62 29 := by
  have hc : ((-450623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418393091171/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-450623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c30 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((8273/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371993/1000000) (δ := 243/50000000) (ψ := -1266091/1000000) 62 34
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t30 : ((3773806647/250000000000 : ℚ) : ℝ) ≤ stT62 30 := by
  have hc : ((2067/25000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3773806647/250000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((2067/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c31 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((855129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1362493/10000000) (δ := 597/100000000) (ψ := -1266091/1000000) 62 34
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t31 : ((1535767203187/10000000000000 : ℚ) : ℝ) ≤ stT62 31 := by
  have hc : ((855079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1535767203187/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((855079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c32 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-809101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6283541/10000000) (δ := 617/100000000) (ψ := -1266091/1000000) 62 34
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t32 : ((-1430390435817/10000000000000 : ℚ) : ℝ) ≤ stT62 32 := by
  have hc : ((-809151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1430390435817/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-809151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c33 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-57407/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -930963/2000000) (δ := 377/100000000) (ψ := -1266091/1000000) 62 35
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t33 : ((-99950193009/2000000000000 : ℚ) : ℝ) ≤ stT62 33 := by
  have hc : ((-57417/200000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99950193009/2000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-57417/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c34 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((999939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13803/5000000) (δ := 243/50000000) (ψ := -1266091/1000000) 62 35
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t34 : ((342958927333/2000000000000 : ℚ) : ℝ) ≤ stT62 34 := by
  have hc : ((999889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342958927333/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((999889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c35 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-213727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2232731/5000000) (δ := 357/100000000) (ψ := -1266091/1000000) 62 35
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t35 : ((-361349187093/10000000000000 : ℚ) : ℝ) ≤ stT62 35 := by
  have hc : ((-213777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361349187093/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-213777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c36 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-924457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1375203/2000000) (δ := 99/25000000) (ψ := -1266091/1000000) 62 36
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t36 : ((-1540845308169/10000000000000 : ℚ) : ℝ) ≤ stT62 36 := by
  have hc : ((-924507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1540845308169/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-924507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c37 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((248061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1314587/5000000) (δ := 139/25000000) (ψ := -1266091/1000000) 62 36
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t37 : ((101942113901/1250000000000 : ℚ) : ℝ) ≤ stT62 37 := by
  have hc : ((62009/125000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101942113901/1250000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((62009/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c38 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((41217/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 376101/2500000) (δ := 347/100000000) (ψ := -1266091/1000000) 62 36
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t38 : ((66858738903/500000000000 : ℚ) : ℝ) ≤ stT62 38 := by
  have hc : ((82429/100000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66858738903/500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((82429/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c39 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-299177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1106121/2000000) (δ := 21/6250000) (ψ := -1266091/1000000) 62 36
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t39 : ((-119776694241/1250000000000 : ℚ) : ℝ) ≤ stT62 39 := by
  have hc : ((-149601/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119776694241/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-149601/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c40 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-160377/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6253099/10000000) (δ := 13/4000000) (ψ := -1266091/1000000) 62 37
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t40 : ((-253594140793/2000000000000 : ℚ) : ℝ) ≤ stT62 40 := by
  have hc : ((-160387/200000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253594140793/2000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-160387/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c41 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((282527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151609/625000) (δ := 189/50000000) (ψ := -1266091/1000000) 62 37
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t41 : ((220596912987/2500000000000 : ℚ) : ℝ) ≤ stT62 41 := by
  have hc : ((141251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220596912987/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((141251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c42 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((865949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1309377/10000000) (δ := 21/4000000) (ψ := -1266091/1000000) 62 37
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t42 : ((1336110731667/10000000000000 : ℚ) : ℝ) ≤ stT62 42 := by
  have hc : ((865899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1336110731667/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((865899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c43 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-400301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239151/2500000) (δ := 109/20000000) (ψ := -1266091/1000000) 62 37
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t43 : ((-305264835043/5000000000000 : ℚ) : ℝ) ≤ stT62 43 := by
  have hc : ((-400351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305264835043/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-400351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c44 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-38589/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449249/625000) (δ := 217/50000000) (ψ := -1266091/1000000) 62 38
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t44 : ((-58178132187/400000000000 : ℚ) : ℝ) ≤ stT62 44 := by
  have hc : ((-38591/40000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58178132187/400000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-38591/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c45 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((88803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3704691/10000000) (δ := 549/100000000) (ψ := -1266091/1000000) 62 38
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t45 : ((132305073383/10000000000000 : ℚ) : ℝ) ≤ stT62 45 := by
  have hc : ((88753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132305073383/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((88753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c46 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((496453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297961/10000000) (δ := 569/100000000) (ψ := -1266091/1000000) 62 38
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t46 : ((182985718833/1250000000000 : ℚ) : ℝ) ≤ stT62 46 := by
  have hc : ((124107/125000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182985718833/1250000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((124107/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c47 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((174543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3035501/10000000) (δ := 317/50000000) (ψ := -1266091/1000000) 62 38
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t47 : ((127280253091/2500000000000 : ℚ) : ℝ) ≤ stT62 47 := by
  have hc : ((87259/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127280253091/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((87259/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c48 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-203167/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 314939/500000) (δ := 277/50000000) (ψ := -1266091/1000000) 62 38
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t48 : ((-36658051749/312500000000 : ℚ) : ℝ) ≤ stT62 48 := by
  have hc : ((-406359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36658051749/312500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-406359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c49 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-396123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3106597/5000000) (δ := 3/500000) (ψ := -1266091/1000000) 62 39
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t49 : ((-35370371291/312500000000 : ℚ) : ℝ) ≤ stT62 49 := by
  have hc : ((-99037/125000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35370371291/312500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-99037/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c50 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((165841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123271/400000) (δ := 623/100000000) (ψ := -1266091/1000000) 62 39
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t50 : ((29312392851/625000000000 : ℚ) : ℝ) ≤ stT62 50 := by
  have hc : ((20727/62500 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29312392851/625000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((20727/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c51 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((249997/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12367/10000000) (δ := 423/100000000) (ψ := -1266091/1000000) 62 39
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t51 : ((17502414783/125000000000 : ℚ) : ℝ) ≤ stT62 51 := by
  have hc : ((499969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17502414783/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((499969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c52 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((363313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 749359/2500000) (δ := 523/100000000) (ψ := -1266091/1000000) 62 39
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t52 : ((2015019861/40000000000 : ℚ) : ℝ) ≤ stT62 52 := by
  have hc : ((363263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2015019861/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((363263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c53 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-11308/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2974953/5000000) (δ := 563/100000000) (ψ := -1266091/1000000) 62 39
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t53 : ((-248540956443/2500000000000 : ℚ) : ℝ) ≤ stT62 53 := by
  have hc : ((-361881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248540956443/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-361881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c54 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-230529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6860777/10000000) (δ := 373/100000000) (ψ := -1266091/1000000) 62 40
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t54 : ((-156863664181/1250000000000 : ℚ) : ℝ) ≤ stT62 54 := by
  have hc : ((-461083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156863664181/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-461083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c55 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-1793/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200833/500000) (δ := 51/10000000) (ψ := -1266091/1000000) 62 40
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t55 : ((-12105261/2500000000 : ℚ) : ℝ) ≤ stT62 55 := by
  have hc : ((-3591/100000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12105261/2500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-3591/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c56 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((2758/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76487/625000) (δ := 53/10000000) (ψ := -1266091/1000000) 62 40
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t56 : ((58965170403/500000000000 : ℚ) : ℝ) ≤ stT62 56 := by
  have hc : ((88251/100000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58965170403/500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((88251/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c57 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((410437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1519643/10000000) (δ := 41/10000000) (ψ := -1266091/1000000) 62 40
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t57 : ((33975239199/312500000000 : ℚ) : ℝ) ≤ stT62 57 := by
  have hc : ((102603/125000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33975239199/312500000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((102603/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c58 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-115093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4215363/10000000) (δ := 573/100000000) (ψ := -1266091/1000000) 62 40
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t58 : ((-30238048659/2000000000000 : ℚ) : ℝ) ≤ stT62 58 := by
  have hc : ((-115143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30238048659/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-115143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c59 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-57673/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1373/2000) (δ := 373/100000000) (ψ := -1266091/1000000) 62 40
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t59 : ((-60070376301/500000000000 : ℚ) : ℝ) ≤ stT62 59 := by
  have hc : ((-461409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60070376301/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-461409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c60 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-199557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311893/500000) (δ := 361/100000000) (ψ := -1266091/1000000) 62 41
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t60 : ((-103057290661/1000000000000 : ℚ) : ℝ) ≤ stT62 60 := by
  have hc : ((-399139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103057290661/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-399139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c61 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((1003/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1837909/5000000) (δ := 381/100000000) (ψ := -1266091/1000000) 62 41
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t61 : ((32089223/2500000000 : ℚ) : ℝ) ≤ stT62 61 := by
  have hc : ((401/4000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32089223/2500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((401/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c62 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((179017/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1155437/10000000) (δ := 521/100000000) (ψ := -1266091/1000000) 62 41
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t62 : ((227339069007/2000000000000 : ℚ) : ℝ) ≤ stT62 62 := by
  have hc : ((179007/200000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227339069007/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((179007/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c63 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((172577/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 165577/1250000) (δ := 231/50000000) (ψ := -1266091/1000000) 62 41
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t63 : ((217413884527/2000000000000 : ℚ) : ℝ) ≤ stT62 63 := by
  have hc : ((172567/200000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217413884527/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((172567/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c64 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((64507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3765611/10000000) (δ := 501/100000000) (ψ := -1266091/1000000) 62 41
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t64 : ((64457/8000000 : ℚ) : ℝ) ≤ stT62 64 := by
  have hc : ((64457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64457/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((64457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c65 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-195319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154219/250000) (δ := 421/100000000) (ψ := -1266091/1000000) 62 41
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t65 : ((-121139517681/1250000000000 : ℚ) : ℝ) ≤ stT62 65 := by
  have hc : ((-390663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121139517681/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-390663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c66 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-481551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1434549/2000000) (δ := 371/100000000) (ψ := -1266091/1000000) 62 42
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t66 : ((-14819478051/125000000000 : ℚ) : ℝ) ≤ stT62 66 := by
  have hc : ((-60197/62500 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14819478051/125000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-60197/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c67 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-4473/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2420937/5000000) (δ := 511/100000000) (ψ := -1266091/1000000) 62 42
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t67 : ((-8744648471/200000000000 : ℚ) : ℝ) ≤ stT62 67 := by
  have hc : ((-35789/100000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8744648471/200000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-35789/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c68 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((524887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19887/78125) (δ := 611/100000000) (ψ := -1266091/1000000) 62 42
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t68 : ((318229141743/5000000000000 : ℚ) : ℝ) ≤ stT62 68 := by
  have hc : ((524837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318229141743/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((524837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c69 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((248403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141361/5000000) (δ := 611/100000000) (ψ := -1266091/1000000) 62 42
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t69 : ((299026890549/2500000000000 : ℚ) : ℝ) ≤ stT62 69 := by
  have hc : ((496781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299026890549/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((496781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c70 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((711607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 486883/2500000) (δ := 391/100000000) (ψ := -1266091/1000000) 62 42
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t70 : ((212618212499/2500000000000 : ℚ) : ℝ) ≤ stT62 70 := by
  have hc : ((711557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212618212499/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((711557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c71 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-1368/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4146151/10000000) (δ := 59/12500000) (ψ := -1266091/1000000) 62 42
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t71 : ((-25991119191/2500000000000 : ℚ) : ℝ) ≤ stT62 71 := by
  have hc : ((-43801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25991119191/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-43801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c72 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-204051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3157009/5000000) (δ := 531/100000000) (ψ := -1266091/1000000) 62 42
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t72 : ((-30061410439/312500000000 : ℚ) : ℝ) ≤ stT62 72 := by
  have hc : ((-408127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30061410439/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-408127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c73 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-121441/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362799/500000) (δ := 381/100000000) (ψ := -1266091/1000000) 62 43
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t73 : ((-142143318767/1250000000000 : ℚ) : ℝ) ≤ stT62 73 := by
  have hc : ((-485789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142143318767/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-485789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c74 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-4689/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160847/312500) (δ := 281/50000000) (ψ := -1266091/1000000) 62 43
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t74 : ((-10902871783/200000000000 : ℚ) : ℝ) ≤ stT62 74 := by
  have hc : ((-9379/20000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10902871783/200000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-9379/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c75 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((337427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -383317/1250000) (δ := 561/100000000) (ψ := -1266091/1000000) 62 43
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t75 : ((3895692219/100000000000 : ℚ) : ℝ) ≤ stT62 75 := by
  have hc : ((337377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3895692219/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((337377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c76 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((918941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -506763/5000000) (δ := 401/100000000) (ψ := -1266091/1000000) 62 43
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t76 : ((527019825249/5000000000000 : ℚ) : ℝ) ≤ stT62 76 := by
  have hc : ((918891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527019825249/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((918891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c77 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((919079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1012647/10000000) (δ := 501/100000000) (ψ := -1266091/1000000) 62 43
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t77 : ((209466008709/2000000000000 : ℚ) : ℝ) ≤ stT62 77 := by
  have hc : ((919029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209466008709/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((919029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c78 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((89407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120507/400000) (δ := 461/100000000) (ψ := -1266091/1000000) 62 43
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t78 : ((202438672553/5000000000000 : ℚ) : ℝ) ≤ stT62 78 := by
  have hc : ((178789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202438672553/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((178789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c79 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-82299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 623403/1250000) (δ := 161/50000000) (ψ := -1266091/1000000) 62 43
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t79 : ((-2893902131/62500000000 : ℚ) : ℝ) ≤ stT62 79 := by
  have hc : ((-82309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2893902131/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-82309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c80 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-933473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1387387/2000000) (δ := 421/100000000) (ψ := -1266091/1000000) 62 43
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t80 : ((-521855226891/5000000000000 : ℚ) : ℝ) ≤ stT62 80 := by
  have hc : ((-933523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521855226891/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-933523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c81 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-919741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3422769/5000000) (δ := 313/100000000) (ψ := -1266091/1000000) 62 44
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t81 : ((-127748852199/1250000000000 : ℚ) : ℝ) ≤ stT62 81 := by
  have hc : ((-919791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127748852199/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-919791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c82 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-98889/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4943673/10000000) (δ := 33/10000000) (ψ := -1266091/1000000) 62 44
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t82 : ((-54609254437/1250000000000 : ℚ) : ℝ) ≤ stT62 82 := by
  have hc : ((-197803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54609254437/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-197803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c83 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((338057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3064863/10000000) (δ := 61/10000000) (ψ := -1266091/1000000) 62 44
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t83 : ((185505339747/5000000000000 : ℚ) : ℝ) ≤ stT62 83 := by
  have hc : ((338007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185505339747/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((338007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c84 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((88541/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1208553/10000000) (δ := 13/2000000) (ψ := -1266091/1000000) 62 44
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t84 : ((12075081963/125000000000 : ℚ) : ℝ) ≤ stT62 84 := by
  have hc : ((11067/12500 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12075081963/125000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((11067/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c85 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((484417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156447/2500000) (δ := 333/100000000) (ψ := -1266091/1000000) 62 44
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t85 : ((16418648487/156250000000 : ℚ) : ℝ) ≤ stT62 85 := by
  have hc : ((60549/62500 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16418648487/156250000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((60549/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c86 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((560779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1219337/5000000) (δ := 573/100000000) (ψ := -1266091/1000000) 62 44
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t86 : ((604649220383/10000000000000 : ℚ) : ℝ) ≤ stT62 86 := by
  have hc : ((560729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((604649220383/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((560729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c87 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-60573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2115301/5000000) (δ := 51/10000000) (ψ := -1266091/1000000) 62 44
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t87 : ((-32483951787/2500000000000 : ℚ) : ℝ) ≤ stT62 87 := by
  have hc : ((-30299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32483951787/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-30299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c88 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-737947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6002049/10000000) (δ := 57/10000000) (ψ := -1266091/1000000) 62 44
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t88 : ((-196676938497/2500000000000 : ℚ) : ℝ) ≤ stT62 88 := by
  have hc : ((-737997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196676938497/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-737997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c89 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-124899/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7753481/10000000) (δ := 433/100000000) (ψ := -1266091/1000000) 62 44
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t89 : ((-264798630379/2500000000000 : ℚ) : ℝ) ≤ stT62 89 := by
  have hc : ((-499621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264798630379/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-499621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c90 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-794541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6222621/10000000) (δ := 53/12500000) (ψ := -1266091/1000000) 62 45
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t90 : ((-837572810963/10000000000000 : ℚ) : ℝ) ≤ stT62 90 := by
  have hc : ((-794591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-837572810963/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-794591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c91 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-14441/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4509897/10000000) (δ := 39/6250000) (ψ := -1266091/1000000) 62 45
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t91 : ((-24226495321/1000000000000 : ℚ) : ℝ) ≤ stT62 91 := by
  have hc : ((-115553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24226495321/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-115553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c92 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((6718/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2815891/10000000) (δ := 111/25000000) (ψ := -1266091/1000000) 62 45
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t92 : ((56025473493/1250000000000 : ℚ) : ℝ) ≤ stT62 92 := by
  have hc : ((214951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56025473493/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((214951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c93 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((448893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1140199/10000000) (δ := 17/3125000) (ψ := -1266091/1000000) 62 45
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t93 : ((116363530367/1250000000000 : ℚ) : ℝ) ≤ stT62 93 := by
  have hc : ((112217/125000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116363530367/1250000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((112217/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c94 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((489323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 517571/10000000) (δ := 121/25000000) (ψ := -1266091/1000000) 62 45
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t94 : ((252336116229/2500000000000 : ℚ) : ℝ) ≤ stT62 94 := by
  have hc : ((244649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252336116229/2500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((244649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c95 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((65007/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1078899/5000000) (δ := 17/3125000) (ψ := -1266091/1000000) 62 45
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t95 : ((16672655489/250000000000 : ℚ) : ℝ) ≤ stT62 95 := by
  have hc : ((32501/50000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16672655489/250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((32501/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c96 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((58423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75617/200000) (δ := 141/25000000) (ψ := -1266091/1000000) 62 45
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t96 : ((2978832563/500000000000 : ℚ) : ℝ) ≤ stT62 96 := by
  have hc : ((58373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2978832563/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((58373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c97 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-137849/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2693541/5000000) (δ := 121/25000000) (ψ := -1266091/1000000) 62 45
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t97 : ((-279954520881/5000000000000 : ℚ) : ℝ) ≤ stT62 97 := by
  have hc : ((-275723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279954520881/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-275723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c98 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-469539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6976839/10000000) (δ := 29/6250000) (ψ := -1266091/1000000) 62 45
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t98 : ((-118582870823/1250000000000 : ℚ) : ℝ) ≤ stT62 98 := by
  have hc : ((-117391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118582870823/1250000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-117391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c99 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-240361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7157507/10000000) (δ := 87/25000000) (ψ := -1266091/1000000) 62 46
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t99 : ((-241584501693/2500000000000 : ℚ) : ℝ) ≤ stT62 99 := by
  have hc : ((-480747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241584501693/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-480747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_c100 :
    |Real.cos (((62 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ))
      - ((-620269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -699963/1250000) (δ := 107/20000000) (ψ := -1266091/1000000) 62 46
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st62_t100 : ((-620319/10000000 : ℚ) : ℝ) ≤ stT62 100 := by
  have hc : ((-620319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((62 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1266091/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st62_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-620319/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-620319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st62_p1 : ((149981/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT62 (i+1) := by
  rw [Finset.sum_range_one]
  exact st62_t1

theorem st62_p2 : ((9834633570339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT62 (i+1))
      = (∑ i ∈ Finset.range 1, stT62 (i+1)) + stT62 2 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 1
    simpa using h
  have hprev := st62_p1
  have hstep := st62_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p3 : ((15406288166917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT62 (i+1))
      = (∑ i ∈ Finset.range 2, stT62 (i+1)) + stT62 3 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 2
    simpa using h
  have hprev := st62_p2
  have hstep := st62_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p4 : ((19070428166917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT62 (i+1))
      = (∑ i ∈ Finset.range 3, stT62 (i+1)) + stT62 4 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 3
    simpa using h
  have hprev := st62_p3
  have hstep := st62_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p5 : ((22950595601237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT62 (i+1))
      = (∑ i ∈ Finset.range 4, stT62 (i+1)) + stT62 5 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 4
    simpa using h
  have hprev := st62_p4
  have hstep := st62_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p6 : ((25959229700921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT62 (i+1))
      = (∑ i ∈ Finset.range 5, stT62 (i+1)) + stT62 6 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 5
    simpa using h
  have hprev := st62_p5
  have hstep := st62_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p7 : ((11430090798213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT62 (i+1))
      = (∑ i ∈ Finset.range 6, stT62 (i+1)) + stT62 7 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 6
    simpa using h
  have hprev := st62_p6
  have hstep := st62_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p8 : ((11105472208469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT62 (i+1))
      = (∑ i ∈ Finset.range 7, stT62 (i+1)) + stT62 8 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 7
    simpa using h
  have hprev := st62_p7
  have hstep := st62_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p9 : ((12340585418291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT62 (i+1))
      = (∑ i ∈ Finset.range 8, stT62 (i+1)) + stT62 9 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 8
    simpa using h
  have hprev := st62_p8
  have hstep := st62_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p10 : ((13737900756281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT62 (i+1))
      = (∑ i ∈ Finset.range 9, stT62 (i+1)) + stT62 10 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 9
    simpa using h
  have hprev := st62_p9
  have hstep := st62_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p11 : ((29440880304521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT62 (i+1))
      = (∑ i ∈ Finset.range 10, stT62 (i+1)) + stT62 11 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 10
    simpa using h
  have hprev := st62_p10
  have hstep := st62_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p12 : ((28928089226249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT62 (i+1))
      = (∑ i ∈ Finset.range 11, stT62 (i+1)) + stT62 12 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 11
    simpa using h
  have hprev := st62_p11
  have hstep := st62_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p13 : ((2616158022227/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT62 (i+1))
      = (∑ i ∈ Finset.range 12, stT62 (i+1)) + stT62 13 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 12
    simpa using h
  have hprev := st62_p12
  have hstep := st62_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p14 : ((13142130565453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT62 (i+1))
      = (∑ i ∈ Finset.range 13, stT62 (i+1)) + stT62 14 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 13
    simpa using h
  have hprev := st62_p13
  have hstep := st62_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p15 : ((14286693571003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT62 (i+1))
      = (∑ i ∈ Finset.range 14, stT62 (i+1)) + stT62 15 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 14
    simpa using h
  have hprev := st62_p14
  have hstep := st62_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p16 : ((26250668712919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT62 (i+1))
      = (∑ i ∈ Finset.range 15, stT62 (i+1)) + stT62 16 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 15
    simpa using h
  have hprev := st62_p15
  have hstep := st62_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p17 : ((27568861825699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT62 (i+1))
      = (∑ i ∈ Finset.range 16, stT62 (i+1)) + stT62 17 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 16
    simpa using h
  have hprev := st62_p16
  have hstep := st62_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p18 : ((27164316540117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT62 (i+1))
      = (∑ i ∈ Finset.range 17, stT62 (i+1)) + stT62 18 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 17
    simpa using h
  have hprev := st62_p17
  have hstep := st62_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p19 : ((27076730175993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT62 (i+1))
      = (∑ i ∈ Finset.range 18, stT62 (i+1)) + stT62 19 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 18
    simpa using h
  have hprev := st62_p18
  have hstep := st62_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p20 : ((13624009808197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT62 (i+1))
      = (∑ i ∈ Finset.range 19, stT62 (i+1)) + stT62 20 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 19
    simpa using h
  have hprev := st62_p19
  have hstep := st62_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p21 : ((6833724667277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT62 (i+1))
      = (∑ i ∈ Finset.range 20, stT62 (i+1)) + stT62 21 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 20
    simpa using h
  have hprev := st62_p20
  have hstep := st62_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p22 : ((6677598787441/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT62 (i+1))
      = (∑ i ∈ Finset.range 21, stT62 (i+1)) + stT62 22 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 21
    simpa using h
  have hprev := st62_p21
  have hstep := st62_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p23 : ((7006491156991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT62 (i+1))
      = (∑ i ∈ Finset.range 22, stT62 (i+1)) + stT62 23 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 22
    simpa using h
  have hprev := st62_p22
  have hstep := st62_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p24 : ((1633382060311/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT62 (i+1))
      = (∑ i ∈ Finset.range 23, stT62 (i+1)) + stT62 24 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 23
    simpa using h
  have hprev := st62_p23
  have hstep := st62_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p25 : ((1755210060311/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT62 (i+1))
      = (∑ i ∈ Finset.range 24, stT62 (i+1)) + stT62 25 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 24
    simpa using h
  have hprev := st62_p24
  have hstep := st62_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p26 : ((13459696833759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT62 (i+1))
      = (∑ i ∈ Finset.range 25, stT62 (i+1)) + stT62 26 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 25
    simpa using h
  have hprev := st62_p25
  have hstep := st62_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p27 : ((6650161566223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT62 (i+1))
      = (∑ i ∈ Finset.range 26, stT62 (i+1)) + stT62 27 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 26
    simpa using h
  have hprev := st62_p26
  have hstep := st62_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p28 : ((7060693268749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT62 (i+1))
      = (∑ i ∈ Finset.range 27, stT62 (i+1)) + stT62 28 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 27
    simpa using h
  have hprev := st62_p27
  have hstep := st62_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p29 : ((3321150088789/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT62 (i+1))
      = (∑ i ∈ Finset.range 28, stT62 (i+1)) + stT62 29 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 28
    simpa using h
  have hprev := st62_p28
  have hstep := st62_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p30 : ((417502390253/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT62 (i+1))
      = (∑ i ∈ Finset.range 29, stT62 (i+1)) + stT62 30 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 29
    simpa using h
  have hprev := st62_p29
  have hstep := st62_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p31 : ((28255920179379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT62 (i+1))
      = (∑ i ∈ Finset.range 30, stT62 (i+1)) + stT62 31 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 30
    simpa using h
  have hprev := st62_p30
  have hstep := st62_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p32 : ((13412764871781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT62 (i+1))
      = (∑ i ∈ Finset.range 31, stT62 (i+1)) + stT62 32 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 31
    simpa using h
  have hprev := st62_p31
  have hstep := st62_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p33 : ((26325778778517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT62 (i+1))
      = (∑ i ∈ Finset.range 32, stT62 (i+1)) + stT62 33 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 32
    simpa using h
  have hprev := st62_p32
  have hstep := st62_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p34 : ((14020286707591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT62 (i+1))
      = (∑ i ∈ Finset.range 33, stT62 (i+1)) + stT62 34 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 33
    simpa using h
  have hprev := st62_p33
  have hstep := st62_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p35 : ((27679224228089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT62 (i+1))
      = (∑ i ∈ Finset.range 34, stT62 (i+1)) + stT62 35 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 34
    simpa using h
  have hprev := st62_p34
  have hstep := st62_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p36 : ((326729736499/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT62 (i+1))
      = (∑ i ∈ Finset.range 35, stT62 (i+1)) + stT62 36 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 35
    simpa using h
  have hprev := st62_p35
  have hstep := st62_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p37 : ((3369239478891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT62 (i+1))
      = (∑ i ∈ Finset.range 36, stT62 (i+1)) + stT62 37 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 36
    simpa using h
  have hprev := st62_p36
  have hstep := st62_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p38 : ((7072772652297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT62 (i+1))
      = (∑ i ∈ Finset.range 37, stT62 (i+1)) + stT62 38 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 37
    simpa using h
  have hprev := st62_p37
  have hstep := st62_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p39 : ((1366643852763/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT62 (i+1))
      = (∑ i ∈ Finset.range 38, stT62 (i+1)) + stT62 39 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 38
    simpa using h
  have hprev := st62_p38
  have hstep := st62_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p40 : ((5212981270259/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT62 (i+1))
      = (∑ i ∈ Finset.range 39, stT62 (i+1)) + stT62 40 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 39
    simpa using h
  have hprev := st62_p39
  have hstep := st62_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p41 : ((26947294003243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT62 (i+1))
      = (∑ i ∈ Finset.range 40, stT62 (i+1)) + stT62 41 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 40
    simpa using h
  have hprev := st62_p40
  have hstep := st62_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p42 : ((2828340473491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT62 (i+1))
      = (∑ i ∈ Finset.range 41, stT62 (i+1)) + stT62 42 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 41
    simpa using h
  have hprev := st62_p41
  have hstep := st62_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p43 : ((3459109383103/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT62 (i+1))
      = (∑ i ∈ Finset.range 42, stT62 (i+1)) + stT62 43 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 42
    simpa using h
  have hprev := st62_p42
  have hstep := st62_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p44 : ((26218421760149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT62 (i+1))
      = (∑ i ∈ Finset.range 43, stT62 (i+1)) + stT62 44 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 43
    simpa using h
  have hprev := st62_p43
  have hstep := st62_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p45 : ((6587681708383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT62 (i+1))
      = (∑ i ∈ Finset.range 44, stT62 (i+1)) + stT62 45 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 44
    simpa using h
  have hprev := st62_p44
  have hstep := st62_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p46 : ((6953653146049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT62 (i+1))
      = (∑ i ∈ Finset.range 45, stT62 (i+1)) + stT62 46 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 45
    simpa using h
  have hprev := st62_p45
  have hstep := st62_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p47 : ((354046669957/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT62 (i+1))
      = (∑ i ∈ Finset.range 46, stT62 (i+1)) + stT62 47 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 46
    simpa using h
  have hprev := st62_p46
  have hstep := st62_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p48 : ((1696917246287/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT62 (i+1))
      = (∑ i ∈ Finset.range 47, stT62 (i+1)) + stT62 48 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 47
    simpa using h
  have hprev := st62_p47
  have hstep := st62_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p49 : ((325235300741/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT62 (i+1))
      = (∑ i ∈ Finset.range 48, stT62 (i+1)) + stT62 49 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 48
    simpa using h
  have hprev := st62_p48
  have hstep := st62_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p50 : ((413872224139/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT62 (i+1))
      = (∑ i ∈ Finset.range 49, stT62 (i+1)) + stT62 50 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 49
    simpa using h
  have hprev := st62_p49
  have hstep := st62_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p51 : ((1743000970471/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT62 (i+1))
      = (∑ i ∈ Finset.range 50, stT62 (i+1)) + stT62 51 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 50
    simpa using h
  have hprev := st62_p50
  have hstep := st62_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p52 : ((14195885246393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT62 (i+1))
      = (∑ i ∈ Finset.range 51, stT62 (i+1)) + stT62 52 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 51
    simpa using h
  have hprev := st62_p51
  have hstep := st62_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p53 : ((13698803333507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT62 (i+1))
      = (∑ i ∈ Finset.range 52, stT62 (i+1)) + stT62 53 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 52
    simpa using h
  have hprev := st62_p52
  have hstep := st62_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p54 : ((13071348676783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT62 (i+1))
      = (∑ i ∈ Finset.range 53, stT62 (i+1)) + stT62 54 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 53
    simpa using h
  have hprev := st62_p53
  have hstep := st62_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p55 : ((13047138154783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT62 (i+1))
      = (∑ i ∈ Finset.range 54, stT62 (i+1)) + stT62 55 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 54
    simpa using h
  have hprev := st62_p54
  have hstep := st62_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p56 : ((13636789858813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT62 (i+1))
      = (∑ i ∈ Finset.range 55, stT62 (i+1)) + stT62 56 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 55
    simpa using h
  have hprev := st62_p55
  have hstep := st62_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p57 : ((14180393685997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT62 (i+1))
      = (∑ i ∈ Finset.range 56, stT62 (i+1)) + stT62 57 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 56
    simpa using h
  have hprev := st62_p56
  have hstep := st62_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p58 : ((28209597128699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT62 (i+1))
      = (∑ i ∈ Finset.range 57, stT62 (i+1)) + stT62 58 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 57
    simpa using h
  have hprev := st62_p57
  have hstep := st62_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p59 : ((27008189602679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT62 (i+1))
      = (∑ i ∈ Finset.range 58, stT62 (i+1)) + stT62 59 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 58
    simpa using h
  have hprev := st62_p58
  have hstep := st62_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p60 : ((25977616696069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT62 (i+1))
      = (∑ i ∈ Finset.range 59, stT62 (i+1)) + stT62 60 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 59
    simpa using h
  have hprev := st62_p59
  have hstep := st62_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p61 : ((26105973588069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT62 (i+1))
      = (∑ i ∈ Finset.range 60, stT62 (i+1)) + stT62 61 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 60
    simpa using h
  have hprev := st62_p60
  have hstep := st62_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p62 : ((1702666808319/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT62 (i+1))
      = (∑ i ∈ Finset.range 61, stT62 (i+1)) + stT62 62 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 61
    simpa using h
  have hprev := st62_p61
  have hstep := st62_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p63 : ((28329738355739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT62 (i+1))
      = (∑ i ∈ Finset.range 62, stT62 (i+1)) + stT62 63 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 62
    simpa using h
  have hprev := st62_p62
  have hstep := st62_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p64 : ((28410309605739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT62 (i+1))
      = (∑ i ∈ Finset.range 63, stT62 (i+1)) + stT62 64 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 63
    simpa using h
  have hprev := st62_p63
  have hstep := st62_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p65 : ((27441193464291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT62 (i+1))
      = (∑ i ∈ Finset.range 64, stT62 (i+1)) + stT62 65 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 64
    simpa using h
  have hprev := st62_p64
  have hstep := st62_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p66 : ((26255635220211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT62 (i+1))
      = (∑ i ∈ Finset.range 65, stT62 (i+1)) + stT62 66 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 65
    simpa using h
  have hprev := st62_p65
  have hstep := st62_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p67 : ((25818402796661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT62 (i+1))
      = (∑ i ∈ Finset.range 66, stT62 (i+1)) + stT62 67 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 66
    simpa using h
  have hprev := st62_p66
  have hstep := st62_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p68 : ((26454861080147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT62 (i+1))
      = (∑ i ∈ Finset.range 67, stT62 (i+1)) + stT62 68 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 67
    simpa using h
  have hprev := st62_p67
  have hstep := st62_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p69 : ((27650968642343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT62 (i+1))
      = (∑ i ∈ Finset.range 68, stT62 (i+1)) + stT62 69 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 68
    simpa using h
  have hprev := st62_p68
  have hstep := st62_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p70 : ((28501441492339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT62 (i+1))
      = (∑ i ∈ Finset.range 69, stT62 (i+1)) + stT62 70 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 69
    simpa using h
  have hprev := st62_p69
  have hstep := st62_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p71 : ((1135899080623/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT62 (i+1))
      = (∑ i ∈ Finset.range 70, stT62 (i+1)) + stT62 71 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 70
    simpa using h
  have hprev := st62_p70
  have hstep := st62_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p72 : ((27435511881527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT62 (i+1))
      = (∑ i ∈ Finset.range 71, stT62 (i+1)) + stT62 72 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 71
    simpa using h
  have hprev := st62_p71
  have hstep := st62_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p73 : ((26298365331391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT62 (i+1))
      = (∑ i ∈ Finset.range 72, stT62 (i+1)) + stT62 73 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 72
    simpa using h
  have hprev := st62_p72
  have hstep := st62_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p74 : ((25753221742241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT62 (i+1))
      = (∑ i ∈ Finset.range 73, stT62 (i+1)) + stT62 74 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 73
    simpa using h
  have hprev := st62_p73
  have hstep := st62_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p75 : ((26142790964141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT62 (i+1))
      = (∑ i ∈ Finset.range 74, stT62 (i+1)) + stT62 75 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 74
    simpa using h
  have hprev := st62_p74
  have hstep := st62_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p76 : ((27196830614639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT62 (i+1))
      = (∑ i ∈ Finset.range 75, stT62 (i+1)) + stT62 76 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 75
    simpa using h
  have hprev := st62_p75
  have hstep := st62_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p77 : ((3530520082273/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT62 (i+1))
      = (∑ i ∈ Finset.range 76, stT62 (i+1)) + stT62 77 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 76
    simpa using h
  have hprev := st62_p76
  have hstep := st62_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p78 : ((2864903800329/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT62 (i+1))
      = (∑ i ∈ Finset.range 77, stT62 (i+1)) + stT62 78 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 77
    simpa using h
  have hprev := st62_p77
  have hstep := st62_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p79 : ((2818601366233/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT62 (i+1))
      = (∑ i ∈ Finset.range 78, stT62 (i+1)) + stT62 79 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 78
    simpa using h
  have hprev := st62_p78
  have hstep := st62_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p80 : ((6785575802137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT62 (i+1))
      = (∑ i ∈ Finset.range 79, stT62 (i+1)) + stT62 80 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 79
    simpa using h
  have hprev := st62_p79
  have hstep := st62_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p81 : ((6530078097739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT62 (i+1))
      = (∑ i ∈ Finset.range 80, stT62 (i+1)) + stT62 81 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 80
    simpa using h
  have hprev := st62_p80
  have hstep := st62_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p82 : ((1284171917773/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT62 (i+1))
      = (∑ i ∈ Finset.range 81, stT62 (i+1)) + stT62 82 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 81
    simpa using h
  have hprev := st62_p81
  have hstep := st62_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p83 : ((13027224517477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT62 (i+1))
      = (∑ i ∈ Finset.range 82, stT62 (i+1)) + stT62 83 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 82
    simpa using h
  have hprev := st62_p82
  have hstep := st62_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p84 : ((13510227795997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT62 (i+1))
      = (∑ i ∈ Finset.range 83, stT62 (i+1)) + stT62 84 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 83
    simpa using h
  have hprev := st62_p83
  have hstep := st62_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p85 : ((14035624547581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT62 (i+1))
      = (∑ i ∈ Finset.range 84, stT62 (i+1)) + stT62 85 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 84
    simpa using h
  have hprev := st62_p84
  have hstep := st62_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p86 : ((5735179663109/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT62 (i+1))
      = (∑ i ∈ Finset.range 85, stT62 (i+1)) + stT62 86 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 85
    simpa using h
  have hprev := st62_p85
  have hstep := st62_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p87 : ((28545962508397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT62 (i+1))
      = (∑ i ∈ Finset.range 86, stT62 (i+1)) + stT62 87 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 86
    simpa using h
  have hprev := st62_p86
  have hstep := st62_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p88 : ((27759254754409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT62 (i+1))
      = (∑ i ∈ Finset.range 87, stT62 (i+1)) + stT62 88 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 87
    simpa using h
  have hprev := st62_p87
  have hstep := st62_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p89 : ((26700060232893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT62 (i+1))
      = (∑ i ∈ Finset.range 88, stT62 (i+1)) + stT62 89 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 88
    simpa using h
  have hprev := st62_p88
  have hstep := st62_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p90 : ((2586248742193/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT62 (i+1))
      = (∑ i ∈ Finset.range 89, stT62 (i+1)) + stT62 90 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 89
    simpa using h
  have hprev := st62_p89
  have hstep := st62_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p91 : ((320252780859/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT62 (i+1))
      = (∑ i ∈ Finset.range 90, stT62 (i+1)) + stT62 91 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 90
    simpa using h
  have hprev := st62_p90
  have hstep := st62_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p92 : ((3258553282083/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT62 (i+1))
      = (∑ i ∈ Finset.range 91, stT62 (i+1)) + stT62 92 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 91
    simpa using h
  have hprev := st62_p91
  have hstep := st62_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p93 : ((67498336249/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT62 (i+1))
      = (∑ i ∈ Finset.range 92, stT62 (i+1)) + stT62 93 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 92
    simpa using h
  have hprev := st62_p92
  have hstep := st62_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p94 : ((7002169741129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT62 (i+1))
      = (∑ i ∈ Finset.range 93, stT62 (i+1)) + stT62 94 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 93
    simpa using h
  have hprev := st62_p93
  have hstep := st62_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p95 : ((7168896296019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT62 (i+1))
      = (∑ i ∈ Finset.range 94, stT62 (i+1)) + stT62 95 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 94
    simpa using h
  have hprev := st62_p94
  have hstep := st62_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p96 : ((3591895229417/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT62 (i+1))
      = (∑ i ∈ Finset.range 95, stT62 (i+1)) + stT62 96 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 95
    simpa using h
  have hprev := st62_p95
  have hstep := st62_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p97 : ((14087626396787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT62 (i+1))
      = (∑ i ∈ Finset.range 96, stT62 (i+1)) + stT62 97 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 96
    simpa using h
  have hprev := st62_p96
  have hstep := st62_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p98 : ((2722658982699/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT62 (i+1))
      = (∑ i ∈ Finset.range 97, stT62 (i+1)) + stT62 98 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 97
    simpa using h
  have hprev := st62_p97
  have hstep := st62_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p99 : ((13130125910109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT62 (i+1))
      = (∑ i ∈ Finset.range 98, stT62 (i+1)) + stT62 99 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 98
    simpa using h
  have hprev := st62_p98
  have hstep := st62_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st62_p100 : ((12819966410109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT62 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT62 (i+1))
      = (∑ i ∈ Finset.range 99, stT62 (i+1)) + stT62 100 := by
    have h := Finset.sum_range_succ (fun i => stT62 (i+1)) 99
    simpa using h
  have hprev := st62_p99
  have hstep := st62_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 62`.** -/
theorem station_62_sign : hardyG (((62:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 62 100 (by norm_num) (by norm_num)
    ((-1266091/1000000 : ℚ) : ℝ)
  have hchain := st62_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT62 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((62:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-1266091/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((62:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((62:ℕ)):ℝ)+1) * ((((62:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((53507/96875 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((12819966410109/5000000000000 : ℚ) : ℝ) - ((53507/96875 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-1266091/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((62:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-1266091/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((62:ℕ)):ℝ))).re
      - Real.sin ((-1266091/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((62:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((62:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((62:ℕ)):ℝ)
      = ((((62:ℕ)):ℝ) * (Real.log (((62:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((62:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_62
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
  have hθwin : |(((-1266091/1000000 : ℚ) : ℝ) + ((7:ℤ)) * (2*Real.pi) - Real.pi) - theta (((62:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((62:ℕ)):ℝ))
    (φ := ((-1266091/1000000 : ℚ) : ℝ) + ((7:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-1266091/1000000 : ℚ) : ℝ) + ((7:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-1266091/1000000 : ℚ)) : ℝ) - Real.pi) + ((7:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-1266091/1000000 : ℚ)) : ℝ) - Real.pi) 7).1,
    (cos_sin_shift ((((-1266091/1000000 : ℚ)) : ℝ) - Real.pi) 7).2]
  exact cos_sin_flip ((-1266091/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_62_sign
end AxiomAudit
