import RequestProject.DVPSqrtTable
import RequestProject.DVPLog200Table

/-!
# Station `t = 102` of the extended Hardy ladder (rung-109)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT102 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((102 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))

theorem st102_c1 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((46851/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 891997/10000000) (δ := 21/100000000) (ψ := -356799/1000000) 102 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t1 : ((93697/100000 : ℚ) : ℝ) ≤ stT102 1 := by
  have hc : ((93697/100000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93697/100000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((93697/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c2 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-363457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1214233/2500000) (δ := 799/100000000) (ψ := -356799/1000000) 102 11
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t2 : ((-642595678869/2500000000000 : ℚ) : ℝ) ≤ stT102 2 := by
  have hc : ((-363507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-642595678869/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-363507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c3 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((776261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213151/1250000) (δ := 447/50000000) (ψ := -356799/1000000) 102 18
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t3 : ((2240727880461/5000000000000 : ℚ) : ℝ) ≤ stT102 3 := by
  have hc : ((776211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2240727880461/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((776211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c4 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-925987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430381/625000) (δ := 19/3125000) (ψ := -356799/1000000) 102 23
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t4 : ((-4630185926037/10000000000000 : ℚ) : ℝ) ≤ stT102 4 := by
  have hc : ((-926037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4630185926037/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-926037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c5 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((40241/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144581/500000) (δ := 903/100000000) (ψ := -356799/1000000) 102 26
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t5 : ((8997041193/50000000000 : ℚ) : ℝ) ≤ stT102 5 := by
  have hc : ((10059/25000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8997041193/50000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((10059/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c6 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((309279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2259727/10000000) (δ := 173/25000000) (ψ := -356799/1000000) 102 29
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t6 : ((315630972107/1250000000000 : ℚ) : ℝ) ≤ stT102 6 := by
  have hc : ((154627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315630972107/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((154627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c7 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-30319/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277787/500000) (δ := 559/100000000) (ψ := -356799/1000000) 102 32
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t7 : ((-45841802347/200000000000 : ℚ) : ℝ) ≤ stT102 7 := by
  have hc : ((-60643/100000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45841802347/200000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-60643/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c8 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((78313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2921161/10000000) (δ := 617/100000000) (ψ := -356799/1000000) 102 34
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t8 : ((276842840499/2000000000000 : ℚ) : ℝ) ≤ stT102 8 := by
  have hc : ((78303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276842840499/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((78303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c9 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-29921/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4302413/10000000) (δ := 787/100000000) (ψ := -356799/1000000) 102 36
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t9 : ((-49885009977/1000000000000 : ℚ) : ℝ) ≤ stT102 9 := by
  have hc : ((-29931/200000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49885009977/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-29931/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c10 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-921461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1371311/2000000) (δ := 469/50000000) (ψ := -356799/1000000) 102 37
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t10 : ((-1457036981029/5000000000000 : ℚ) : ℝ) ≤ stT102 10 := by
  have hc : ((-921511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1457036981029/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-921511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c11 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((994791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63819/2500000) (δ := 9/1250000) (ψ := -356799/1000000) 102 39
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t11 : ((2999256520733/10000000000000 : ℚ) : ℝ) ≤ stT102 11 := by
  have hc : ((994741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2999256520733/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((994741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c12 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-795037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3112331/5000000) (δ := 533/100000000) (ψ := -356799/1000000) 102 40
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t12 : ((-71725593357/312500000000 : ℚ) : ℝ) ≤ stT102 12 := by
  have hc : ((-795087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71725593357/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-795087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c13 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-334763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2390187/5000000) (δ := 143/25000000) (ψ := -356799/1000000) 102 42
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t13 : ((-928604190313/10000000000000 : ℚ) : ℝ) ≤ stT102 13 := by
  have hc : ((-334813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-928604190313/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-334813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c14 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((804287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -397701/2500000) (δ := 721/100000000) (ψ := -356799/1000000) 102 43
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t14 : ((537353364261/2500000000000 : ℚ) : ℝ) ≤ stT102 14 := by
  have hc : ((804237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537353364261/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((804237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c15 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((496537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147207/5000000) (δ := 21/2000000) (ψ := -356799/1000000) 102 44
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t15 : ((2503882863/9765625000 : ℚ) : ℝ) ≤ stT102 15 := by
  have hc : ((15516/15625 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2503882863/9765625000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((15516/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c16 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((457051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 521887/5000000) (δ := 819/100000000) (ψ := -356799/1000000) 102 45
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t16 : ((228513/1000000 : ℚ) : ℝ) ≤ stT102 16 := by
  have hc : ((228513/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228513/1000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((228513/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c17 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((237463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 795089/10000000) (δ := 19/3125000) (ψ := -356799/1000000) 102 46
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t17 : ((287950997439/1250000000000 : ℚ) : ℝ) ≤ stT102 17 := by
  have hc : ((474901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287950997439/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((474901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c18 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((990903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168739/5000000) (δ := 117/20000000) (ψ := -356799/1000000) 102 47
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t18 : ((1167731159883/5000000000000 : ℚ) : ℝ) ≤ stT102 18 := by
  have hc : ((990853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1167731159883/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((990853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c19 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((309503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22583/100000) (δ := 199/25000000) (ψ := -356799/1000000) 102 48
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t19 : ((354995560023/2500000000000 : ℚ) : ℝ) ≤ stT102 19 := by
  have hc : ((154739/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354995560023/2500000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((154739/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c20 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-9361/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4886473/10000000) (δ := 747/100000000) (ψ := -356799/1000000) 102 49
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t20 : ((-20934627633/250000000000 : ℚ) : ℝ) ≤ stT102 20 := by
  have hc : ((-37449/100000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20934627633/250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-37449/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c21 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-496429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3777509/5000000) (δ := 169/25000000) (ψ := -356799/1000000) 102 49
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t21 : ((-541675746633/2500000000000 : ℚ) : ℝ) ≤ stT102 21 := by
  have hc : ((-248227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-541675746633/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-248227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c22 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((86823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3709659/10000000) (δ := 517/100000000) (ψ := -356799/1000000) 102 50
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t22 : ((185000643411/10000000000000 : ℚ) : ℝ) ≤ stT102 22 := by
  have hc : ((86773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185000643411/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((86773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c23 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((965029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132621/2000000) (δ := 179/20000000) (ψ := -356799/1000000) 102 51
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t23 : ((251515021497/1250000000000 : ℚ) : ℝ) ≤ stT102 23 := by
  have hc : ((964979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251515021497/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((964979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c24 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-23777/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2759183/5000000) (δ := 181/25000000) (ψ := -356799/1000000) 102 52
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t24 : ((-24269346759/200000000000 : ℚ) : ℝ) ≤ stT102 24 := by
  have hc : ((-23779/40000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24269346759/200000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-23779/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c25 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-23513/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2445621/5000000) (δ := 201/25000000) (ψ := -356799/1000000) 102 52
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t25 : ((-376258188129/5000000000000 : ℚ) : ℝ) ≤ stT102 25 := by
  have hc : ((-188129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376258188129/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-188129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c26 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((37891/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -815439/10000000) (δ := 653/100000000) (ψ := -356799/1000000) 102 53
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t26 : ((74306429129/400000000000 : ℚ) : ℝ) ≤ stT102 26 := by
  have hc : ((37889/40000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74306429129/400000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((37889/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c27 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-58001/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6899619/10000000) (δ := 1/156250) (ψ := -356799/1000000) 102 54
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t27 : ((-893031972533/5000000000000 : ℚ) : ℝ) ≤ stT102 27 := by
  have hc : ((-464033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-893031972533/5000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-464033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c28 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((290983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2374131/10000000) (δ := 923/100000000) (ψ := -356799/1000000) 102 54
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t28 : ((137464707369/1250000000000 : ℚ) : ℝ) ≤ stT102 28 := by
  have hc : ((145479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137464707369/1250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((145479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c29 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-36479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2192773/5000000) (δ := 183/25000000) (ψ := -356799/1000000) 102 55
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t29 : ((-33879197253/1000000000000 : ℚ) : ℝ) ≤ stT102 29 := by
  have hc : ((-36489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33879197253/1000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-36489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c30 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-16569/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85187/200000) (δ := 831/100000000) (ψ := -356799/1000000) 102 55
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t30 : ((-60524260171/2500000000000 : ℚ) : ℝ) ≤ stT102 30 := by
  have hc : ((-66301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60524260171/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-66301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c31 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((329631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3087209/10000000) (δ := 1001/100000000) (ψ := -356799/1000000) 102 56
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t31 : ((591944943793/10000000000000 : ℚ) : ℝ) ≤ stT102 31 := by
  have hc : ((329581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((591944943793/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((329581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c32 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-26207/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5008709/10000000) (δ := 1021/100000000) (ψ := -356799/1000000) 102 56
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t32 : ((-370667152327/5000000000000 : ℚ) : ℝ) ≤ stT102 32 := by
  have hc : ((-209681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370667152327/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-209681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c33 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((416693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2852481/10000000) (δ := 153/25000000) (ψ := -356799/1000000) 102 57
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t33 : ((90660266871/1250000000000 : ℚ) : ℝ) ≤ stT102 33 := by
  have hc : ((416643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90660266871/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((416643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c34 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-163541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 190401/400000) (δ := 771/100000000) (ψ := -356799/1000000) 102 57
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t34 : ((-70128350019/1250000000000 : ℚ) : ℝ) ≤ stT102 34 := by
  have hc : ((-81783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70128350019/1250000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-81783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c35 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((73903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3556117/10000000) (δ := 603/100000000) (ψ := -356799/1000000) 102 58
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t35 : ((15609571803/625000000000 : ℚ) : ℝ) ≤ stT102 35 := by
  have hc : ((36939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15609571803/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((36939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c36 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((119527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3627457/10000000) (δ := 1/156250) (ψ := -356799/1000000) 102 58
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t36 : ((99564126841/5000000000000 : ℚ) : ℝ) ≤ stT102 36 := by
  have hc : ((119477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99564126841/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((119477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c37 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-449951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636721/1250000) (δ := 909/100000000) (ψ := -356799/1000000) 102 59
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t37 : ((-73979714399/1000000000000 : ℚ) : ℝ) ≤ stT102 37 := by
  have hc : ((-450001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73979714399/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-450001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c38 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((775901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 341327/2000000) (δ := 297/50000000) (ψ := -356799/1000000) 102 59
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t38 : ((629298177057/5000000000000 : ℚ) : ℝ) ≤ stT102 38 := by
  have hc : ((775851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((629298177057/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((775851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c39 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-490949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7377579/10000000) (δ := 279/50000000) (ψ := -356799/1000000) 102 60
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t39 : ((-196546957167/1250000000000 : ℚ) : ℝ) ≤ stT102 39 := by
  have hc : ((-245487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196546957167/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-245487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c40 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((932827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460769/5000000) (δ := 109/20000000) (ψ := -356799/1000000) 102 60
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t40 : ((737424580113/5000000000000 : ℚ) : ℝ) ≤ stT102 40 := by
  have hc : ((932777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((737424580113/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((932777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c41 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-68423/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2687539/5000000) (δ := 133/20000000) (ψ := -356799/1000000) 102 60
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t41 : ((-213737120073/2500000000000 : ℚ) : ℝ) ≤ stT102 41 := by
  have hc : ((-273717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213737120073/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-273717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c42 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-52109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418801/1000000) (δ := 217/25000000) (ψ := -356799/1000000) 102 61
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t42 : ((-20111133639/1250000000000 : ℚ) : ℝ) ≤ stT102 42 := by
  have hc : ((-26067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20111133639/1250000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-26067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c43 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((748561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1812267/10000000) (δ := 111/12500000) (ψ := -356799/1000000) 102 61
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t43 : ((228293609467/2000000000000 : ℚ) : ℝ) ≤ stT102 43 := by
  have hc : ((748511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228293609467/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((748511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c44 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-997427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3837297/5000000) (δ := 177/25000000) (ψ := -356799/1000000) 102 61
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t44 : ((-1503753433689/10000000000000 : ℚ) : ℝ) ≤ stT102 44 := by
  have hc : ((-997477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1503753433689/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-997477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c45 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((151233/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2302791/10000000) (δ := 443/50000000) (ψ := -356799/1000000) 102 62
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t45 : ((450852125551/5000000000000 : ℚ) : ℝ) ≤ stT102 45 := by
  have hc : ((302441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450852125551/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((302441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c46 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((123733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330183/1000000) (δ := 473/50000000) (ψ := -356799/1000000) 102 62
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t46 : ((45599356413/1250000000000 : ℚ) : ℝ) ≤ stT102 46 := by
  have hc : ((30927/125000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45599356413/1250000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((30927/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c47 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-931321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138441/200000) (δ := 503/50000000) (ψ := -356799/1000000) 102 63
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t47 : ((-27170886183/200000000000 : ℚ) : ℝ) ≤ stT102 47 := by
  have hc : ((-931371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27170886183/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-931371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c48 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((20327/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1553431/10000000) (δ := 463/50000000) (ψ := -356799/1000000) 102 63
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t48 : ((938805741/8000000000 : ℚ) : ℝ) ≤ stT102 48 := by
  have hc : ((81303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((938805741/8000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((81303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c49 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((22221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3704487/10000000) (δ := 977/100000000) (ψ := -356799/1000000) 102 63
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t49 : ((63452838107/5000000000000 : ℚ) : ℝ) ≤ stT102 49 := by
  have hc : ((44417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63452838107/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((44417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c50 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-920719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3425893/5000000) (δ := 249/25000000) (ψ := -356799/1000000) 102 64
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t50 : ((-651082205283/5000000000000 : ℚ) : ℝ) ≤ stT102 50 := by
  have hc : ((-920769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-651082205283/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-920769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c51 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((751247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -450529/2500000) (δ := 179/25000000) (ψ := -356799/1000000) 102 64
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t51 : ((26297153379/250000000000 : ℚ) : ℝ) ≤ stT102 51 := by
  have hc : ((751197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26297153379/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((751197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c52 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((306009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393687/1250000) (δ := 107/12500000) (ψ := -356799/1000000) 102 64
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t52 : ((1697154573/40000000000 : ℚ) : ℝ) ≤ stT102 52 := by
  have hc : ((305959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1697154573/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((305959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c53 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-998133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7701177/10000000) (δ := 177/20000000) (ψ := -356799/1000000) 102 65
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t53 : ((-685555078949/5000000000000 : ℚ) : ℝ) ≤ stT102 53 := by
  have hc : ((-998183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685555078949/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-998183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c54 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((193291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -733671/2500000) (δ := 117/20000000) (ψ := -356799/1000000) 102 65
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t54 : ((131500795491/2500000000000 : ℚ) : ℝ) ≤ stT102 54 := by
  have hc : ((96633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131500795491/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((96633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c55 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((766297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1744347/10000000) (δ := 429/50000000) (ψ := -356799/1000000) 102 65
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t55 : ((1033206688553/10000000000000 : ℚ) : ℝ) ≤ stT102 55 := by
  have hc : ((766247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1033206688553/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((766247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c56 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-12843/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3169533/5000000) (δ := 459/50000000) (ψ := -356799/1000000) 102 65
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t56 : ((-549223513307/5000000000000 : ℚ) : ℝ) ≤ stT102 56 := by
  have hc : ((-411001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-549223513307/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-411001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c57 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-181463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -971101/2000000) (δ := 689/100000000) (ψ := -356799/1000000) 102 66
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t57 : ((-15024177819/312500000000 : ℚ) : ℝ) ≤ stT102 57 := by
  have hc : ((-11343/31250 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15024177819/312500000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-11343/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c58 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((24647/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -420611/10000000) (δ := 467/50000000) (ψ := -356799/1000000) 102 66
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t58 : ((16180723539/125000000000 : ℚ) : ℝ) ≤ stT102 58 := by
  have hc : ((98583/100000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16180723539/125000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((98583/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c59 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-287/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393847/1000000) (δ := 287/50000000) (ψ := -356799/1000000) 102 66
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t59 : ((-302168669/500000000000 : ℚ) : ℝ) ≤ stT102 59 := by
  have hc : ((-2321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302168669/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-2321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c60 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-19781/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7483679/10000000) (δ := 3/500000) (ψ := -356799/1000000) 102 67
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t60 : ((-2553846309/20000000000 : ℚ) : ℝ) ≤ stT102 60 := by
  have hc : ((-9891/10000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2553846309/20000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-9891/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c61 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((260281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3268707/10000000) (δ := 31/5000000) (ψ := -356799/1000000) 102 67
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t61 : ((20824465313/625000000000 : ℚ) : ℝ) ≤ stT102 61 := by
  have hc : ((260231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20824465313/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((260231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c62 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((469499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 438863/5000000) (δ := 21/2500000) (ψ := -356799/1000000) 102 67
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t62 : ((298116224737/2500000000000 : ℚ) : ℝ) ≤ stT102 62 := by
  have hc : ((234737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298116224737/2500000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((234737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c63 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-50093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4957813/10000000) (δ := 783/100000000) (ψ := -356799/1000000) 102 67
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t63 : ((-126238286577/2500000000000 : ℚ) : ℝ) ≤ stT102 63 := by
  have hc : ((-200397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126238286577/2500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-200397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c64 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-450687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6734319/10000000) (δ := 83/10000000) (ψ := -356799/1000000) 102 68
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t64 : ((-70423806339/625000000000 : ℚ) : ℝ) ≤ stT102 64 := by
  have hc : ((-56339/62500 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70423806339/625000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-56339/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c65 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((2213/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2780751/10000000) (δ := 71/10000000) (ψ := -356799/1000000) 102 68
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t65 : ((10978311297/200000000000 : ℚ) : ℝ) ≤ stT102 65 := by
  have hc : ((8851/20000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10978311297/200000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((8851/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c66 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((902619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 556227/5000000) (δ := 613/100000000) (ψ := -356799/1000000) 102 68
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t66 : ((555492409033/5000000000000 : ℚ) : ℝ) ≤ stT102 66 := by
  have hc : ((902569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((555492409033/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((902569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c67 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-396819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4947113/10000000) (δ := 833/100000000) (ψ := -356799/1000000) 102 68
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t67 : ((-96970574591/2000000000000 : ℚ) : ℝ) ≤ stT102 67 := by
  have hc : ((-396869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96970574591/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-396869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c68 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-939923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1745751/2500000) (δ := 501/50000000) (ψ := -356799/1000000) 102 69
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t68 : ((-1139885517667/10000000000000 : ℚ) : ℝ) ≤ stT102 68 := by
  have hc : ((-939973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1139885517667/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-939973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c69 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((263523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326031/1000000) (δ := 501/50000000) (ψ := -356799/1000000) 102 69
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t69 : ((158592039417/5000000000000 : ℚ) : ℝ) ≤ stT102 69 := by
  have hc : ((263473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158592039417/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((263473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c70 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((986659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 204409/5000000) (δ := 311/50000000) (ψ := -356799/1000000) 102 69
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t70 : ((294805675463/2500000000000 : ℚ) : ℝ) ≤ stT102 70 := by
  have hc : ((986609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294805675463/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((986609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c71 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-39553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40259/100000) (δ := 761/100000000) (ψ := -356799/1000000) 102 69
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t71 : ((-23500063773/5000000000000 : ℚ) : ℝ) ≤ stT102 71 := by
  have hc : ((-39603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23500063773/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-39603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c72 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-994531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 949049/1250000) (δ := 421/50000000) (ψ := -356799/1000000) 102 69
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t72 : ((-73257852717/625000000000 : ℚ) : ℝ) ≤ stT102 72 := by
  have hc : ((-994581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73257852717/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-994581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c73 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-132649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2299137/5000000) (δ := 611/100000000) (ψ := -356799/1000000) 102 70
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t73 : ((-19410405211/625000000000 : ℚ) : ℝ) ≤ stT102 73 := by
  have hc : ((-66337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19410405211/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-66337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c74 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((899779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1128833/10000000) (δ := 233/25000000) (ψ := -356799/1000000) 102 70
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t74 : ((261478342251/2500000000000 : ℚ) : ℝ) ≤ stT102 74 := by
  have hc : ((899729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261478342251/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((899729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c75 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((151929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2294037/10000000) (δ := 911/100000000) (ψ := -356799/1000000) 102 70
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t75 : ((3508359651/50000000000 : ℚ) : ℝ) ≤ stT102 75 := by
  have hc : ((303833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3508359651/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((303833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c76 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-321279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 567157/1000000) (δ := 631/100000000) (ψ := -356799/1000000) 102 70
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t76 : ((-46070133877/625000000000 : ℚ) : ℝ) ≤ stT102 76 := by
  have hc : ((-40163/62500 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46070133877/625000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-40163/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c77 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-22397/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1675753/2500000) (δ := 801/100000000) (ψ := -356799/1000000) 102 71
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t77 : ((-51050360179/500000000000 : ℚ) : ℝ) ≤ stT102 77 := by
  have hc : ((-89593/100000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51050360179/500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-89593/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c78 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((20429/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -853161/2500000) (δ := 761/100000000) (ψ := -356799/1000000) 102 71
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t78 : ((2890703181/125000000000 : ℚ) : ℝ) ≤ stT102 78 := by
  have hc : ((2553/12500 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2890703181/125000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((2553/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c79 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((249461/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164193/10000000) (δ := 521/100000000) (ψ := -356799/1000000) 102 71
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t79 : ((561302529039/5000000000000 : ℚ) : ℝ) ≤ stT102 79 := by
  have hc : ((498897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((561302529039/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((498897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c80 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((2769/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3043397/10000000) (δ := 681/100000000) (ψ := -356799/1000000) 102 71
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t80 : ((15476930819/400000000000 : ℚ) : ℝ) ≤ stT102 80 := by
  have hc : ((13843/40000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15476930819/400000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((13843/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c81 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-12371/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6211139/10000000) (δ := 261/50000000) (ψ := -356799/1000000) 102 71
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t81 : ((-54985738433/625000000000 : ℚ) : ℝ) ≤ stT102 81 := by
  have hc : ((-395897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54985738433/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-395897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c82 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-414239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127359/200000) (δ := 11/2000000) (ψ := -356799/1000000) 102 72
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t82 : ((-14296198857/156250000000 : ℚ) : ℝ) ≤ stT102 82 := by
  have hc : ((-51783/62500 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14296198857/156250000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-51783/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c83 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((64269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3277003/10000000) (δ := 19/2000000) (ψ := -356799/1000000) 102 72
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t83 : ((70530633173/2500000000000 : ℚ) : ℝ) ≤ stT102 83 := by
  have hc : ((128513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70530633173/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((128513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c84 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((498011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8923/400000) (δ := 107/10000000) (ψ := -356799/1000000) 102 72
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t84 : ((271673523377/2500000000000 : ℚ) : ℝ) ≤ stT102 84 := by
  have hc : ((248993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271673523377/2500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((248993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c85 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((87517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 349339/1250000) (δ := 553/100000000) (ψ := -356799/1000000) 102 72
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t85 : ((23728660641/500000000000 : ℚ) : ℝ) ≤ stT102 85 := by
  have hc : ((87507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23728660641/500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((87507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c86 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-13487/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2888601/5000000) (δ := 953/100000000) (ψ := -356799/1000000) 102 72
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t86 : ((-113628813/1562500000 : ℚ) : ℝ) ≤ stT102 86 := by
  have hc : ((-843/1250 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113628813/1562500000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-843/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c87 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-939889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6982751/10000000) (δ := 839/100000000) (ψ := -356799/1000000) 102 73
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t87 : ((-1007720821107/10000000000000 : ℚ) : ℝ) ≤ stT102 87 := by
  have hc : ((-939939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1007720821107/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-939939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c88 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-56547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2034217/5000000) (δ := 899/100000000) (ψ := -356799/1000000) 102 73
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t88 : ((-15083157097/2500000000000 : ℚ) : ℝ) ≤ stT102 88 := by
  have hc : ((-56597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15083157097/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-56597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c89 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((27793/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1187047/10000000) (δ := 11/1562500) (ψ := -356799/1000000) 102 73
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t89 : ((471341446011/5000000000000 : ℚ) : ℝ) ≤ stT102 89 := by
  have hc : ((444663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471341446011/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((444663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c90 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((157401/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25971/156250) (δ := 171/25000000) (ψ := -356799/1000000) 102 73
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t90 : ((41476148493/500000000000 : ℚ) : ℝ) ≤ stT102 90 := by
  have hc : ((157391/200000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41476148493/500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((157391/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c91 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-219347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4479853/10000000) (δ := 271/25000000) (ψ := -356799/1000000) 102 73
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t91 : ((-45998116829/2000000000000 : ℚ) : ℝ) ≤ stT102 91 := by
  have hc : ((-219397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45998116829/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-219397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c92 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-972541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3633383/5000000) (δ := 49/6250000) (ψ := -356799/1000000) 102 73
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t92 : ((-1013997116643/10000000000000 : ℚ) : ℝ) ≤ stT102 92 := by
  have hc : ((-972591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1013997116643/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-972591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c93 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-323243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2842207/5000000) (δ := 187/20000000) (ψ := -356799/1000000) 102 74
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t93 : ((-10475418723/156250000000 : ℚ) : ℝ) ≤ stT102 93 := by
  have hc : ((-80817/125000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10475418723/156250000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-80817/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c94 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((94573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -591423/2000000) (δ := 167/20000000) (ψ := -356799/1000000) 102 74
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t94 : ((195063370941/5000000000000 : ℚ) : ℝ) ≤ stT102 94 := by
  have hc : ((189121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195063370941/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((189121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c95 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((248663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258677/10000000) (δ := 187/20000000) (ψ := -356799/1000000) 102 74
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t95 : ((255109942689/2500000000000 : ℚ) : ℝ) ≤ stT102 95 := by
  have hc : ((497301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255109942689/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((497301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c96 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((35609/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150719/625000) (δ := 183/20000000) (ψ := -356799/1000000) 102 74
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t96 : ((14536027257/250000000000 : ℚ) : ℝ) ≤ stT102 96 := by
  have hc : ((284847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14536027257/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((284847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c97 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-217847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1010803/2000000) (δ := 159/20000000) (ψ := -356799/1000000) 102 74
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t97 : ((-13825980099/312500000000 : ℚ) : ℝ) ≤ stT102 97 := by
  have hc : ((-13617/31250 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13825980099/312500000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-13617/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c98 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-249319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3834711/5000000) (δ := 31/4000000) (ψ := -356799/1000000) 102 74
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t98 : ((-503725925439/5000000000000 : ℚ) : ℝ) ≤ stT102 98 := by
  have hc : ((-498663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503725925439/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-498663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c99 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((-35757/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2724843/5000000) (δ := 259/50000000) (ψ := -356799/1000000) 102 75
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t99 : ((-143761138039/2500000000000 : ℚ) : ℝ) ≤ stT102 99 := by
  have hc : ((-286081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143761138039/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-286081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_c100 :
    |Real.cos (((102 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ))
      - ((101039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2886851/10000000) (δ := 169/20000000) (ψ := -356799/1000000) 102 75
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st102_t100 : ((202052797947/5000000000000 : ℚ) : ℝ) ≤ stT102 100 := by
  have hc : ((202053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((102 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-356799/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st102_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202052797947/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((202053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st102_p1 : ((93697/100000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT102 (i+1) := by
  rw [Finset.sum_range_one]
  exact st102_t1

theorem st102_p2 : ((1699829321131/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT102 (i+1))
      = (∑ i ∈ Finset.range 1, stT102 (i+1)) + stT102 2 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 1
    simpa using h
  have hprev := st102_p1
  have hstep := st102_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p3 : ((5640386522723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT102 (i+1))
      = (∑ i ∈ Finset.range 2, stT102 (i+1)) + stT102 3 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 2
    simpa using h
  have hprev := st102_p2
  have hstep := st102_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p4 : ((6650587119409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT102 (i+1))
      = (∑ i ∈ Finset.range 3, stT102 (i+1)) + stT102 4 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 3
    simpa using h
  have hprev := st102_p3
  have hstep := st102_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p5 : ((8449995358009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT102 (i+1))
      = (∑ i ∈ Finset.range 4, stT102 (i+1)) + stT102 5 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 4
    simpa using h
  have hprev := st102_p4
  have hstep := st102_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p6 : ((2195008626973/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT102 (i+1))
      = (∑ i ∈ Finset.range 5, stT102 (i+1)) + stT102 6 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 5
    simpa using h
  have hprev := st102_p5
  have hstep := st102_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p7 : ((1736590603503/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT102 (i+1))
      = (∑ i ∈ Finset.range 6, stT102 (i+1)) + stT102 7 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 6
    simpa using h
  have hprev := st102_p6
  have hstep := st102_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p8 : ((1006716722001/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT102 (i+1))
      = (∑ i ∈ Finset.range 7, stT102 (i+1)) + stT102 8 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 7
    simpa using h
  have hprev := st102_p7
  have hstep := st102_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p9 : ((119603964003/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT102 (i+1))
      = (∑ i ∈ Finset.range 8, stT102 (i+1)) + stT102 9 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 8
    simpa using h
  have hprev := st102_p8
  have hstep := st102_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p10 : ((3327121579091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT102 (i+1))
      = (∑ i ∈ Finset.range 9, stT102 (i+1)) + stT102 10 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 9
    simpa using h
  have hprev := st102_p9
  have hstep := st102_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p11 : ((1930699935783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT102 (i+1))
      = (∑ i ∈ Finset.range 10, stT102 (i+1)) + stT102 11 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 10
    simpa using h
  have hprev := st102_p10
  have hstep := st102_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p12 : ((7358280691491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT102 (i+1))
      = (∑ i ∈ Finset.range 11, stT102 (i+1)) + stT102 12 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 11
    simpa using h
  have hprev := st102_p11
  have hstep := st102_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p13 : ((3214838250589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT102 (i+1))
      = (∑ i ∈ Finset.range 12, stT102 (i+1)) + stT102 13 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 12
    simpa using h
  have hprev := st102_p12
  have hstep := st102_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p14 : ((4289544979111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT102 (i+1))
      = (∑ i ∈ Finset.range 13, stT102 (i+1)) + stT102 14 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 13
    simpa using h
  have hprev := st102_p13
  have hstep := st102_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p15 : ((5571533004967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT102 (i+1))
      = (∑ i ∈ Finset.range 14, stT102 (i+1)) + stT102 15 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 14
    simpa using h
  have hprev := st102_p14
  have hstep := st102_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p16 : ((6714098004967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT102 (i+1))
      = (∑ i ∈ Finset.range 15, stT102 (i+1)) + stT102 16 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 15
    simpa using h
  have hprev := st102_p15
  have hstep := st102_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p17 : ((7865901994723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT102 (i+1))
      = (∑ i ∈ Finset.range 16, stT102 (i+1)) + stT102 17 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 16
    simpa using h
  have hprev := st102_p16
  have hstep := st102_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p18 : ((4516816577303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT102 (i+1))
      = (∑ i ∈ Finset.range 17, stT102 (i+1)) + stT102 18 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 17
    simpa using h
  have hprev := st102_p17
  have hstep := st102_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p19 : ((2435906068663/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT102 (i+1))
      = (∑ i ∈ Finset.range 18, stT102 (i+1)) + stT102 19 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 18
    simpa using h
  have hprev := st102_p18
  have hstep := st102_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p20 : ((1165616465249/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT102 (i+1))
      = (∑ i ∈ Finset.range 19, stT102 (i+1)) + stT102 20 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 19
    simpa using h
  have hprev := st102_p19
  have hstep := st102_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p21 : ((4120790114363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT102 (i+1))
      = (∑ i ∈ Finset.range 20, stT102 (i+1)) + stT102 21 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 20
    simpa using h
  have hprev := st102_p20
  have hstep := st102_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p22 : ((16668161100863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT102 (i+1))
      = (∑ i ∈ Finset.range 21, stT102 (i+1)) + stT102 22 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 21
    simpa using h
  have hprev := st102_p21
  have hstep := st102_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p23 : ((18680281272839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT102 (i+1))
      = (∑ i ∈ Finset.range 22, stT102 (i+1)) + stT102 23 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 22
    simpa using h
  have hprev := st102_p22
  have hstep := st102_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p24 : ((17466813934889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT102 (i+1))
      = (∑ i ∈ Finset.range 23, stT102 (i+1)) + stT102 24 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 23
    simpa using h
  have hprev := st102_p23
  have hstep := st102_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p25 : ((16714297558631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT102 (i+1))
      = (∑ i ∈ Finset.range 24, stT102 (i+1)) + stT102 25 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 24
    simpa using h
  have hprev := st102_p24
  have hstep := st102_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p26 : ((2321494785857/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT102 (i+1))
      = (∑ i ∈ Finset.range 25, stT102 (i+1)) + stT102 26 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 25
    simpa using h
  have hprev := st102_p25
  have hstep := st102_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p27 : ((1678589434179/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT102 (i+1))
      = (∑ i ∈ Finset.range 26, stT102 (i+1)) + stT102 27 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 26
    simpa using h
  have hprev := st102_p26
  have hstep := st102_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p28 : ((8942806000371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT102 (i+1))
      = (∑ i ∈ Finset.range 27, stT102 (i+1)) + stT102 28 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 27
    simpa using h
  have hprev := st102_p27
  have hstep := st102_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p29 : ((4386705007053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT102 (i+1))
      = (∑ i ∈ Finset.range 28, stT102 (i+1)) + stT102 29 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 28
    simpa using h
  have hprev := st102_p28
  have hstep := st102_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p30 : ((2163090373441/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT102 (i+1))
      = (∑ i ∈ Finset.range 29, stT102 (i+1)) + stT102 30 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 29
    simpa using h
  have hprev := st102_p29
  have hstep := st102_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p31 : ((17896667931321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT102 (i+1))
      = (∑ i ∈ Finset.range 30, stT102 (i+1)) + stT102 31 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 30
    simpa using h
  have hprev := st102_p30
  have hstep := st102_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p32 : ((17155333626667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT102 (i+1))
      = (∑ i ∈ Finset.range 31, stT102 (i+1)) + stT102 32 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 31
    simpa using h
  have hprev := st102_p31
  have hstep := st102_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p33 : ((3576123152327/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT102 (i+1))
      = (∑ i ∈ Finset.range 32, stT102 (i+1)) + stT102 33 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 32
    simpa using h
  have hprev := st102_p32
  have hstep := st102_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p34 : ((17319588961483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT102 (i+1))
      = (∑ i ∈ Finset.range 33, stT102 (i+1)) + stT102 34 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 33
    simpa using h
  have hprev := st102_p33
  have hstep := st102_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p35 : ((17569342110331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT102 (i+1))
      = (∑ i ∈ Finset.range 34, stT102 (i+1)) + stT102 35 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 34
    simpa using h
  have hprev := st102_p34
  have hstep := st102_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p36 : ((17768470364013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT102 (i+1))
      = (∑ i ∈ Finset.range 35, stT102 (i+1)) + stT102 36 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 35
    simpa using h
  have hprev := st102_p35
  have hstep := st102_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p37 : ((17028673220023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT102 (i+1))
      = (∑ i ∈ Finset.range 36, stT102 (i+1)) + stT102 37 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 36
    simpa using h
  have hprev := st102_p36
  have hstep := st102_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p38 : ((18287269574137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT102 (i+1))
      = (∑ i ∈ Finset.range 37, stT102 (i+1)) + stT102 38 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 37
    simpa using h
  have hprev := st102_p37
  have hstep := st102_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p39 : ((16714893916801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT102 (i+1))
      = (∑ i ∈ Finset.range 38, stT102 (i+1)) + stT102 39 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 38
    simpa using h
  have hprev := st102_p38
  have hstep := st102_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p40 : ((18189743077027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT102 (i+1))
      = (∑ i ∈ Finset.range 39, stT102 (i+1)) + stT102 40 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 39
    simpa using h
  have hprev := st102_p39
  have hstep := st102_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p41 : ((3466958919347/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT102 (i+1))
      = (∑ i ∈ Finset.range 40, stT102 (i+1)) + stT102 41 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 40
    simpa using h
  have hprev := st102_p40
  have hstep := st102_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p42 : ((17173905527623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT102 (i+1))
      = (∑ i ∈ Finset.range 41, stT102 (i+1)) + stT102 42 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 41
    simpa using h
  have hprev := st102_p41
  have hstep := st102_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p43 : ((9157686787479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT102 (i+1))
      = (∑ i ∈ Finset.range 42, stT102 (i+1)) + stT102 43 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 42
    simpa using h
  have hprev := st102_p42
  have hstep := st102_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p44 : ((16811620141269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT102 (i+1))
      = (∑ i ∈ Finset.range 43, stT102 (i+1)) + stT102 44 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 43
    simpa using h
  have hprev := st102_p43
  have hstep := st102_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p45 : ((17713324392371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT102 (i+1))
      = (∑ i ∈ Finset.range 44, stT102 (i+1)) + stT102 45 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 44
    simpa using h
  have hprev := st102_p44
  have hstep := st102_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p46 : ((723124769747/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT102 (i+1))
      = (∑ i ∈ Finset.range 45, stT102 (i+1)) + stT102 46 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 45
    simpa using h
  have hprev := st102_p45
  have hstep := st102_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p47 : ((668782997381/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT102 (i+1))
      = (∑ i ∈ Finset.range 46, stT102 (i+1)) + stT102 47 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 46
    simpa using h
  have hprev := st102_p46
  have hstep := st102_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p48 : ((715723284431/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT102 (i+1))
      = (∑ i ∈ Finset.range 47, stT102 (i+1)) + stT102 48 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 47
    simpa using h
  have hprev := st102_p47
  have hstep := st102_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p49 : ((18019987786989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT102 (i+1))
      = (∑ i ∈ Finset.range 48, stT102 (i+1)) + stT102 49 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 48
    simpa using h
  have hprev := st102_p48
  have hstep := st102_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p50 : ((16717823376423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT102 (i+1))
      = (∑ i ∈ Finset.range 49, stT102 (i+1)) + stT102 50 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 49
    simpa using h
  have hprev := st102_p49
  have hstep := st102_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p51 : ((17769709511583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT102 (i+1))
      = (∑ i ∈ Finset.range 50, stT102 (i+1)) + stT102 51 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 50
    simpa using h
  have hprev := st102_p50
  have hstep := st102_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p52 : ((18193998154833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT102 (i+1))
      = (∑ i ∈ Finset.range 51, stT102 (i+1)) + stT102 52 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 51
    simpa using h
  have hprev := st102_p51
  have hstep := st102_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p53 : ((3364577599387/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT102 (i+1))
      = (∑ i ∈ Finset.range 52, stT102 (i+1)) + stT102 53 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 52
    simpa using h
  have hprev := st102_p52
  have hstep := st102_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p54 : ((17348891178899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT102 (i+1))
      = (∑ i ∈ Finset.range 53, stT102 (i+1)) + stT102 54 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 53
    simpa using h
  have hprev := st102_p53
  have hstep := st102_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p55 : ((4595524466863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT102 (i+1))
      = (∑ i ∈ Finset.range 54, stT102 (i+1)) + stT102 55 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 54
    simpa using h
  have hprev := st102_p54
  have hstep := st102_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p56 : ((8641825420419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT102 (i+1))
      = (∑ i ∈ Finset.range 55, stT102 (i+1)) + stT102 56 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 55
    simpa using h
  have hprev := st102_p55
  have hstep := st102_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p57 : ((1680287715063/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT102 (i+1))
      = (∑ i ∈ Finset.range 56, stT102 (i+1)) + stT102 57 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 56
    simpa using h
  have hprev := st102_p56
  have hstep := st102_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p58 : ((14477868027/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT102 (i+1))
      = (∑ i ∈ Finset.range 57, stT102 (i+1)) + stT102 58 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 57
    simpa using h
  have hprev := st102_p57
  have hstep := st102_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p59 : ((1809129166037/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT102 (i+1))
      = (∑ i ∈ Finset.range 58, stT102 (i+1)) + stT102 59 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 58
    simpa using h
  have hprev := st102_p58
  have hstep := st102_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p60 : ((1681436850587/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT102 (i+1))
      = (∑ i ∈ Finset.range 59, stT102 (i+1)) + stT102 60 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 59
    simpa using h
  have hprev := st102_p59
  have hstep := st102_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p61 : ((8573779975439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT102 (i+1))
      = (∑ i ∈ Finset.range 60, stT102 (i+1)) + stT102 61 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 60
    simpa using h
  have hprev := st102_p60
  have hstep := st102_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p62 : ((9170012424913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT102 (i+1))
      = (∑ i ∈ Finset.range 61, stT102 (i+1)) + stT102 62 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 61
    simpa using h
  have hprev := st102_p61
  have hstep := st102_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p63 : ((8917535851759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT102 (i+1))
      = (∑ i ∈ Finset.range 62, stT102 (i+1)) + stT102 63 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 62
    simpa using h
  have hprev := st102_p62
  have hstep := st102_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p64 : ((8354145401047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT102 (i+1))
      = (∑ i ∈ Finset.range 63, stT102 (i+1)) + stT102 64 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 63
    simpa using h
  have hprev := st102_p63
  have hstep := st102_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p65 : ((539287698967/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT102 (i+1))
      = (∑ i ∈ Finset.range 64, stT102 (i+1)) + stT102 65 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 64
    simpa using h
  have hprev := st102_p64
  have hstep := st102_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p66 : ((1836819118501/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT102 (i+1))
      = (∑ i ∈ Finset.range 65, stT102 (i+1)) + stT102 66 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 65
    simpa using h
  have hprev := st102_p65
  have hstep := st102_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p67 : ((3576667662411/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT102 (i+1))
      = (∑ i ∈ Finset.range 66, stT102 (i+1)) + stT102 67 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 66
    simpa using h
  have hprev := st102_p66
  have hstep := st102_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p68 : ((4185863198597/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT102 (i+1))
      = (∑ i ∈ Finset.range 67, stT102 (i+1)) + stT102 68 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 67
    simpa using h
  have hprev := st102_p67
  have hstep := st102_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p69 : ((8530318436611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT102 (i+1))
      = (∑ i ∈ Finset.range 68, stT102 (i+1)) + stT102 69 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 68
    simpa using h
  have hprev := st102_p68
  have hstep := st102_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p70 : ((9119929787537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT102 (i+1))
      = (∑ i ∈ Finset.range 69, stT102 (i+1)) + stT102 70 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 69
    simpa using h
  have hprev := st102_p69
  have hstep := st102_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p71 : ((2274107430941/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT102 (i+1))
      = (∑ i ∈ Finset.range 70, stT102 (i+1)) + stT102 71 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 70
    simpa using h
  have hprev := st102_p70
  have hstep := st102_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p72 : ((2127591725507/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT102 (i+1))
      = (∑ i ∈ Finset.range 71, stT102 (i+1)) + stT102 72 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 71
    simpa using h
  have hprev := st102_p71
  have hstep := st102_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p73 : ((417754183017/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT102 (i+1))
      = (∑ i ∈ Finset.range 72, stT102 (i+1)) + stT102 73 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 72
    simpa using h
  have hprev := st102_p72
  have hstep := st102_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p74 : ((4439020172421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT102 (i+1))
      = (∑ i ∈ Finset.range 73, stT102 (i+1)) + stT102 74 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 73
    simpa using h
  have hprev := st102_p73
  have hstep := st102_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p75 : ((4614438154971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT102 (i+1))
      = (∑ i ∈ Finset.range 74, stT102 (i+1)) + stT102 75 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 74
    simpa using h
  have hprev := st102_p74
  have hstep := st102_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p76 : ((4430157619463/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT102 (i+1))
      = (∑ i ∈ Finset.range 75, stT102 (i+1)) + stT102 76 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 75
    simpa using h
  have hprev := st102_p75
  have hstep := st102_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p77 : ((521863227321/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT102 (i+1))
      = (∑ i ∈ Finset.range 76, stT102 (i+1)) + stT102 77 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 76
    simpa using h
  have hprev := st102_p76
  have hstep := st102_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p78 : ((1058179970547/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT102 (i+1))
      = (∑ i ∈ Finset.range 77, stT102 (i+1)) + stT102 78 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 77
    simpa using h
  have hprev := st102_p77
  have hstep := st102_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p79 : ((1805348458683/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT102 (i+1))
      = (∑ i ∈ Finset.range 78, stT102 (i+1)) + stT102 79 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 78
    simpa using h
  have hprev := st102_p78
  have hstep := st102_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p80 : ((3688081571461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT102 (i+1))
      = (∑ i ∈ Finset.range 79, stT102 (i+1)) + stT102 80 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 79
    simpa using h
  have hprev := st102_p79
  have hstep := st102_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p81 : ((17560636042377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT102 (i+1))
      = (∑ i ∈ Finset.range 80, stT102 (i+1)) + stT102 81 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 80
    simpa using h
  have hprev := st102_p80
  have hstep := st102_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p82 : ((16645679315529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT102 (i+1))
      = (∑ i ∈ Finset.range 81, stT102 (i+1)) + stT102 82 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 81
    simpa using h
  have hprev := st102_p81
  have hstep := st102_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p83 : ((16927801848221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT102 (i+1))
      = (∑ i ∈ Finset.range 82, stT102 (i+1)) + stT102 83 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 82
    simpa using h
  have hprev := st102_p82
  have hstep := st102_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p84 : ((18014495941729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT102 (i+1))
      = (∑ i ∈ Finset.range 83, stT102 (i+1)) + stT102 84 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 83
    simpa using h
  have hprev := st102_p83
  have hstep := st102_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p85 : ((18489069154549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT102 (i+1))
      = (∑ i ∈ Finset.range 84, stT102 (i+1)) + stT102 85 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 84
    simpa using h
  have hprev := st102_p84
  have hstep := st102_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p86 : ((17761844751349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT102 (i+1))
      = (∑ i ∈ Finset.range 85, stT102 (i+1)) + stT102 86 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 85
    simpa using h
  have hprev := st102_p85
  have hstep := st102_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p87 : ((8377061965121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT102 (i+1))
      = (∑ i ∈ Finset.range 86, stT102 (i+1)) + stT102 87 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 86
    simpa using h
  have hprev := st102_p86
  have hstep := st102_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p88 : ((8346895650927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT102 (i+1))
      = (∑ i ∈ Finset.range 87, stT102 (i+1)) + stT102 88 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 87
    simpa using h
  have hprev := st102_p87
  have hstep := st102_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p89 : ((4409118548469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT102 (i+1))
      = (∑ i ∈ Finset.range 88, stT102 (i+1)) + stT102 89 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 88
    simpa using h
  have hprev := st102_p88
  have hstep := st102_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p90 : ((2308249645467/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT102 (i+1))
      = (∑ i ∈ Finset.range 89, stT102 (i+1)) + stT102 90 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 89
    simpa using h
  have hprev := st102_p89
  have hstep := st102_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p91 : ((18236006579591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT102 (i+1))
      = (∑ i ∈ Finset.range 90, stT102 (i+1)) + stT102 91 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 90
    simpa using h
  have hprev := st102_p90
  have hstep := st102_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p92 : ((4305502365737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT102 (i+1))
      = (∑ i ∈ Finset.range 91, stT102 (i+1)) + stT102 92 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 91
    simpa using h
  have hprev := st102_p91
  have hstep := st102_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p93 : ((4137895666169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT102 (i+1))
      = (∑ i ∈ Finset.range 92, stT102 (i+1)) + stT102 93 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 92
    simpa using h
  have hprev := st102_p92
  have hstep := st102_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p94 : ((8470854703279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT102 (i+1))
      = (∑ i ∈ Finset.range 93, stT102 (i+1)) + stT102 94 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 93
    simpa using h
  have hprev := st102_p93
  have hstep := st102_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p95 : ((8981074588657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT102 (i+1))
      = (∑ i ∈ Finset.range 94, stT102 (i+1)) + stT102 95 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 94
    simpa using h
  have hprev := st102_p94
  have hstep := st102_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p96 : ((9271795133797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT102 (i+1))
      = (∑ i ∈ Finset.range 95, stT102 (i+1)) + stT102 96 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 95
    simpa using h
  have hprev := st102_p95
  have hstep := st102_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p97 : ((9050579452213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT102 (i+1))
      = (∑ i ∈ Finset.range 96, stT102 (i+1)) + stT102 97 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 96
    simpa using h
  have hprev := st102_p96
  have hstep := st102_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p98 : ((4273426763387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT102 (i+1))
      = (∑ i ∈ Finset.range 97, stT102 (i+1)) + stT102 98 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 97
    simpa using h
  have hprev := st102_p97
  have hstep := st102_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p99 : ((1032416406337/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT102 (i+1))
      = (∑ i ∈ Finset.range 98, stT102 (i+1)) + stT102 99 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 98
    simpa using h
  have hprev := st102_p98
  have hstep := st102_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st102_p100 : ((8461384048643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT102 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT102 (i+1))
      = (∑ i ∈ Finset.range 99, stT102 (i+1)) + stT102 100 := by
    have h := Finset.sum_range_succ (fun i => stT102 (i+1)) 99
    simpa using h
  have hprev := st102_p99
  have hstep := st102_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 102`.** -/
theorem station_102_sign : hardyG (((102:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 102 100 (by norm_num) (by norm_num)
    ((-356799/1000000 : ℚ) : ℝ)
  have hchain := st102_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT102 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((102:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-356799/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((102:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((102:ℕ)):ℝ)+1) * ((((102:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1791963/1700000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8461384048643/5000000000000 : ℚ) : ℝ) - ((1791963/1700000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-356799/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((102:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-356799/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((102:ℕ)):ℝ))).re
      - Real.sin ((-356799/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((102:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((102:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((102:ℕ)):ℝ)
      = ((((102:ℕ)):ℝ) * (Real.log (((102:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((102:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_102
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
  have hθwin : |(((-356799/1000000 : ℚ) : ℝ) + ((15:ℤ)) * (2*Real.pi) - Real.pi) - theta (((102:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((102:ℕ)):ℝ))
    (φ := ((-356799/1000000 : ℚ) : ℝ) + ((15:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-356799/1000000 : ℚ) : ℝ) + ((15:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-356799/1000000 : ℚ)) : ℝ) - Real.pi) + ((15:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-356799/1000000 : ℚ)) : ℝ) - Real.pi) 15).1,
    (cos_sin_shift ((((-356799/1000000 : ℚ)) : ℝ) - Real.pi) 15).2]
  exact cos_sin_flip ((-356799/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_102_sign
end AxiomAudit
