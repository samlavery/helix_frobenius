import RequestProject.DVPSqrtTable

/-!
# Station `t = 97` of the extended Hardy ladder (rung-109)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT97 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((97 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))

theorem st97_c1 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((557819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1223801/5000000) (δ := 21/100000000) (ψ := -979041/1000000) 97 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t1 : ((557769/1000000 : ℚ) : ℝ) ≤ stT97 1 := by
  have hc : ((557769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((557769/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((557769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c2 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((124209/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2251803/10000000) (δ := 749/100000000) (ψ := -979041/1000000) 97 11
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t2 : ((878219450333/2000000000000 : ℚ) : ℝ) ≤ stT97 2 := by
  have hc : ((124199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((878219450333/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((124199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c3 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((372493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912853/5000000) (δ := 103/12500000) (ψ := -979041/1000000) 97 17
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t3 : ((268805592867/625000000000 : ℚ) : ℝ) ≤ stT97 3 := by
  have hc : ((93117/125000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268805592867/625000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((93117/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c4 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-187101/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6951207/10000000) (δ := 587/100000000) (ψ := -979041/1000000) 97 22
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t4 : ((-935555187111/2000000000000 : ℚ) : ℝ) ≤ stT97 4 := by
  have hc : ((-187111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-935555187111/2000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-187111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c5 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((999889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18607/5000000) (δ := 437/50000000) (ψ := -979041/1000000) 97 25
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t5 : ((894282997253/2000000000000 : ℚ) : ℝ) ≤ stT97 5 := by
  have hc : ((999839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((894282997253/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((999839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c6 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((408963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1436849/5000000) (δ := 331/50000000) (ψ := -979041/1000000) 97 28
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t6 : ((834689981033/5000000000000 : ℚ) : ℝ) ≤ stT97 6 := by
  have hc : ((408913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((834689981033/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((408913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c7 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((327853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 618383/2000000) (δ := 13/2500000) (ψ := -979041/1000000) 97 30
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t7 : ((309744660533/2500000000000 : ℚ) : ℝ) ≤ stT97 7 := by
  have hc : ((327803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309744660533/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((327803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c8 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-1303/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4057351/10000000) (δ := 599/100000000) (ψ := -979041/1000000) 97 32
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t8 : ((-9222440439/500000000000 : ℚ) : ℝ) ≤ stT97 8 := by
  have hc : ((-5217/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9222440439/500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-5217/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c9 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((88629/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1203811/10000000) (δ := 23/3125000) (ψ := -979041/1000000) 97 34
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t9 : ((18463331487/62500000000 : ℚ) : ℝ) ≤ stT97 9 := by
  have hc : ((5539/6250 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18463331487/62500000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((5539/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c10 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-14493/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4662191/10000000) (δ := 867/100000000) (ψ := -979041/1000000) 97 36
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t10 : ((-45838800749/500000000000 : ℚ) : ℝ) ≤ stT97 10 := by
  have hc : ((-28991/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45838800749/500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-28991/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c11 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((91249/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548513/2000000) (δ := 349/50000000) (ψ := -979041/1000000) 97 37
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t11 : ((275095895007/2000000000000 : ℚ) : ℝ) ≤ stT97 11 := by
  have hc : ((91239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275095895007/2000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((91239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c12 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-198739/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7573103/10000000) (δ := 513/100000000) (ψ := -979041/1000000) 97 39
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t12 : ((-17929346039/62500000000 : ℚ) : ℝ) ≤ stT97 12 := by
  have hc : ((-198749/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17929346039/62500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-198749/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c13 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((2251/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387071/1000000) (δ := 13/2500000) (ψ := -979041/1000000) 97 40
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t13 : ((6229281/1000000000 : ℚ) : ℝ) ≤ stT97 13 := by
  have hc : ((1123/50000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6229281/1000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((1123/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c14 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((800303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160749/1000000) (δ := 361/50000000) (ψ := -979041/1000000) 97 41
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t14 : ((534691442709/2500000000000 : ℚ) : ℝ) ≤ stT97 14 := by
  have hc : ((800253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((534691442709/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((800253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c15 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((121597/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -584681/10000000) (δ := 961/100000000) (ψ := -979041/1000000) 97 42
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t15 : ((313945857411/1250000000000 : ℚ) : ℝ) ≤ stT97 15 := by
  have hc : ((486363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313945857411/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((486363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c16 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((483601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -642053/10000000) (δ := 761/100000000) (ψ := -979041/1000000) 97 43
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t16 : ((60447/250000 : ℚ) : ℝ) ≤ stT97 16 := by
  have hc : ((60447/62500 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60447/250000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((60447/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c17 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((790349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -824273/5000000) (δ := 57/10000000) (ψ := -979041/1000000) 97 44
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t17 : ((479189105361/2500000000000 : ℚ) : ℝ) ≤ stT97 17 := by
  have hc : ((790299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((479189105361/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((790299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c18 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((21463/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1747797/5000000) (δ := 267/50000000) (ψ := -979041/1000000) 97 45
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t18 : ((101148063597/2500000000000 : ℚ) : ℝ) ≤ stT97 18 := by
  have hc : ((85827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101148063597/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((85827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c19 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-190453/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190383/312500) (δ := 149/20000000) (ψ := -979041/1000000) 97 46
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t19 : ((-436957950549/2500000000000 : ℚ) : ℝ) ≤ stT97 19 := by
  have hc : ((-380931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436957950549/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-380931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c20 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-205903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49581/78125) (δ := 139/20000000) (ψ := -979041/1000000) 97 46
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t20 : ((-230220530127/1250000000000 : ℚ) : ℝ) ≤ stT97 20 := by
  have hc : ((-411831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230220530127/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-411831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c21 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((275177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123501/500000) (δ := 19/3125000) (ψ := -979041/1000000) 97 47
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t21 : ((18763457533/156250000000 : ℚ) : ℝ) ≤ stT97 21 := by
  have hc : ((17197/31250 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18763457533/156250000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((17197/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c22 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((708987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48921/250000) (δ := 31/6250000) (ψ := -979041/1000000) 97 48
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t22 : ((1511458646559/10000000000000 : ℚ) : ℝ) ≤ stT97 22 := by
  have hc : ((708937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1511458646559/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((708937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c23 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-46293/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6885251/10000000) (δ := 423/50000000) (ψ := -979041/1000000) 97 49
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t23 : ((-38613132139/200000000000 : ℚ) : ℝ) ≤ stT97 23 := by
  have hc : ((-92591/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38613132139/200000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-92591/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c24 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((3907/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53679/156250) (δ := 343/50000000) (ψ := -979041/1000000) 97 49
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t24 : ((3986543673/100000000000 : ℚ) : ℝ) ≤ stT97 24 := by
  have hc : ((1953/10000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3986543673/100000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((1953/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c25 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((582277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1186587/5000000) (δ := 189/25000000) (ψ := -979041/1000000) 97 50
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t25 : ((582227/5000000 : ℚ) : ℝ) ≤ stT97 25 := by
  have hc : ((582227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((582227/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((582227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c26 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-239813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7137849/10000000) (δ := 313/50000000) (ψ := -979041/1000000) 97 50
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t26 : ((-470336657231/2500000000000 : ℚ) : ℝ) ≤ stT97 26 := by
  have hc : ((-479651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470336657231/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-479651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c27 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((121629/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116383/2000000) (δ := 19/3125000) (ψ := -979041/1000000) 97 51
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t27 : ((1872503859/10000000000 : ℚ) : ℝ) ≤ stT97 27 := by
  have hc : ((486491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1872503859/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((486491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c28 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-162911/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3153447/5000000) (δ := 221/25000000) (ψ := -979041/1000000) 97 52
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t28 : ((-307891852983/2000000000000 : ℚ) : ℝ) ≤ stT97 28 := by
  have hc : ((-162921/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307891852983/2000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-162921/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c29 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((636303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2202751/10000000) (δ := 347/50000000) (ψ := -979041/1000000) 97 52
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t29 : ((1181491917109/10000000000000 : ℚ) : ℝ) ≤ stT97 29 := by
  have hc : ((636253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1181491917109/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((636253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c30 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-64571/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2642043/5000000) (δ := 39/5000000) (ψ := -979041/1000000) 97 53
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t30 : ((-235802795139/2500000000000 : ℚ) : ℝ) ≤ stT97 30 := by
  have hc : ((-258309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235802795139/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-258309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c31 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((482773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1333723/5000000) (δ := 943/100000000) (ψ := -979041/1000000) 97 53
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t31 : ((866996092319/10000000000000 : ℚ) : ℝ) ≤ stT97 31 := by
  have hc : ((482723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((866996092319/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((482723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c32 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-6701/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2670729/5000000) (δ := 963/100000000) (ψ := -979041/1000000) 97 54
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t32 : ((-94775292171/1000000000000 : ℚ) : ℝ) ≤ stT97 32 := by
  have hc : ((-53613/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94775292171/1000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-53613/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c33 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((165321/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2120669/10000000) (δ := 57/10000000) (ψ := -979041/1000000) 97 54
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t33 : ((71941267349/625000000000 : ℚ) : ℝ) ≤ stT97 33 := by
  have hc : ((330617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71941267349/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((330617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c34 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-823971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6347951/10000000) (δ := 193/25000000) (ψ := -979041/1000000) 97 55
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t34 : ((-706592239353/5000000000000 : ℚ) : ℝ) ≤ stT97 34 := by
  have hc : ((-824021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-706592239353/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-824021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c35 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((963071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 681527/10000000) (δ := 571/100000000) (ψ := -979041/1000000) 97 55
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t35 : ((406950525117/2500000000000 : ℚ) : ℝ) ≤ stT97 35 := by
  have hc : ((963021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((406950525117/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((963021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c36 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-990711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1502593/2000000) (δ := 153/25000000) (ψ := -979041/1000000) 97 55
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t36 : ((-1651268663587/10000000000000 : ℚ) : ℝ) ≤ stT97 36 := by
  have hc : ((-990761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1651268663587/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-990761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c37 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((162741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1550747/10000000) (δ := 861/100000000) (ψ := -979041/1000000) 97 56
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t37 : ((267527973959/2000000000000 : ℚ) : ℝ) ≤ stT97 37 := by
  have hc : ((162731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267527973959/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((162731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c38 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-385477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4916303/10000000) (δ := 143/25000000) (ψ := -979041/1000000) 97 56
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t38 : ((-125081536461/2000000000000 : ℚ) : ℝ) ≤ stT97 38 := by
  have hc : ((-385527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125081536461/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-385527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c39 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-701/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -898521/2000000) (δ := 541/100000000) (ψ := -979041/1000000) 97 57
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t39 : ((-17963982117/500000000000 : ℚ) : ℝ) ≤ stT97 39 := by
  have hc : ((-22437/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17963982117/500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-22437/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c40 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((49421/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1646963/10000000) (δ := 123/25000000) (ψ := -979041/1000000) 97 57
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t40 : ((312545920167/2500000000000 : ℚ) : ℝ) ≤ stT97 40 := by
  have hc : ((395343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312545920167/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((395343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c41 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-996163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3817461/5000000) (δ := 79/12500000) (ψ := -979041/1000000) 97 57
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t41 : ((-777911849097/5000000000000 : ℚ) : ℝ) ≤ stT97 41 := by
  have hc : ((-996213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-777911849097/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-996213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c42 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((39253/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -445877/2000000) (δ := 81/10000000) (ψ := -979041/1000000) 97 58
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t42 : ((484510818967/5000000000000 : ℚ) : ℝ) ≤ stT97 42 := by
  have hc : ((313999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484510818967/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((313999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c43 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((2239/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3476761/10000000) (δ := 41/5000000) (ψ := -979041/1000000) 97 58
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t43 : ((5461581279/200000000000 : ℚ) : ℝ) ≤ stT97 43 := by
  have hc : ((17907/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5461581279/200000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((17907/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c44 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-887413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331249/2000000) (δ := 679/100000000) (ψ := -979041/1000000) 97 59
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t44 : ((-1337901057891/10000000000000 : ℚ) : ℝ) ≤ stT97 44 := by
  have hc : ((-887463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1337901057891/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-887463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c45 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((885777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1206577/10000000) (δ := 427/50000000) (ψ := -979041/1000000) 97 59
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t45 : ((1320362981897/10000000000000 : ℚ) : ℝ) ≤ stT97 45 := by
  have hc : ((885727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1320362981897/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((885727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c46 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-39223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1030827/2500000) (δ := 231/25000000) (ψ := -979041/1000000) 97 59
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t46 : ((-180837613/15625000000 : ℚ) : ℝ) ≤ stT97 46 := by
  have hc : ((-2453/31250 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180837613/15625000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-2453/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c47 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-414401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6369401/10000000) (δ := 247/25000000) (ψ := -979041/1000000) 97 60
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t47 : ((-6045024849/50000000000 : ℚ) : ℝ) ≤ stT97 47 := by
  have hc : ((-207213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6045024849/50000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-207213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c48 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((437447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263949/10000000) (δ := 111/12500000) (ψ := -979041/1000000) 97 60
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t48 : ((2525455917/20000000000 : ℚ) : ℝ) ≤ stT97 48 := by
  have hc : ((218711/250000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2525455917/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((218711/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c49 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((76231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934057/2500000) (δ := 37/4000000) (ψ := -979041/1000000) 97 60
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t49 : ((108829967351/10000000000000 : ℚ) : ℝ) ≤ stT97 49 := by
  have hc : ((76181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108829967351/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((76181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c50 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-951549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7072579/10000000) (δ := 479/50000000) (ψ := -979041/1000000) 97 61
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t50 : ((-672882314093/5000000000000 : ℚ) : ℝ) ≤ stT97 50 := by
  have hc : ((-951599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-672882314093/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-951599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c51 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((38449/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2270441/10000000) (δ := 329/50000000) (ψ := -979041/1000000) 97 61
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t51 : ((10766997969/125000000000 : ℚ) : ℝ) ≤ stT97 51 := by
  have hc : ((307567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10766997969/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((307567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c52 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((112171/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609611/2500000) (δ := 207/25000000) (ψ := -979041/1000000) 97 61
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t52 : ((622157067/8000000000 : ℚ) : ℝ) ≤ stT97 52 := by
  have hc : ((112161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((622157067/8000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((112161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c53 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-474847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220551/312500) (δ := 53/6250000) (ψ := -979041/1000000) 97 61
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t53 : ((-40767939277/312500000000 : ℚ) : ℝ) ≤ stT97 53 := by
  have hc : ((-59359/62500 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40767939277/312500000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-59359/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c54 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-38063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4117489/10000000) (δ := 527/100000000) (ψ := -979041/1000000) 97 62
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t54 : ((-1619725527/156250000000 : ℚ) : ℝ) ≤ stT97 54 := by
  have hc : ((-4761/62500 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1619725527/156250000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-4761/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c55 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((495593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332177/10000000) (δ := 51/6250000) (ψ := -979041/1000000) 97 62
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t55 : ((41763962227/312500000000 : ℚ) : ℝ) ≤ stT97 55 := by
  have hc : ((30973/31250 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41763962227/312500000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((30973/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c56 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-152467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146927/312500) (δ := 423/50000000) (ψ := -979041/1000000) 97 62
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t56 : ((-50944031761/1250000000000 : ℚ) : ℝ) ≤ stT97 56 := by
  have hc : ((-38123/125000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50944031761/1250000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-38123/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c57 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-897851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6714151/10000000) (δ := 657/100000000) (ψ := -979041/1000000) 97 63
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t57 : ((-1189299505233/10000000000000 : ℚ) : ℝ) ≤ stT97 57 := by
  have hc : ((-897901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1189299505233/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-897901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c58 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((135357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1248327/5000000) (δ := 7/781250) (ψ := -979041/1000000) 97 63
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t58 : ((44428997637/625000000000 : ℚ) : ℝ) ≤ stT97 58 := by
  have hc : ((270689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44428997637/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((270689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c59 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((7903/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 824373/5000000) (δ := 9/1562500) (ψ := -979041/1000000) 97 63
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t59 : ((4115271129/40000000000 : ℚ) : ℝ) ≤ stT97 59 := by
  have hc : ((3161/4000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4115271129/40000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((3161/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c60 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-658627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715559/1250000) (δ := 567/100000000) (ψ := -979041/1000000) 97 63
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t60 : ((-170069742723/2000000000000 : ℚ) : ℝ) ≤ stT97 60 := by
  have hc : ((-658677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170069742723/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-658677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c61 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-730639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1195027/2000000) (δ := 607/100000000) (ψ := -979041/1000000) 97 64
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t61 : ((-935551544241/10000000000000 : ℚ) : ℝ) ≤ stT97 61 := by
  have hc : ((-730689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-935551544241/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-730689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c62 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((17187/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2031959/10000000) (δ := 797/100000000) (ψ := -979041/1000000) 97 64
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t62 : ((87303678743/1000000000000 : ℚ) : ℝ) ≤ stT97 62 := by
  have hc : ((68743/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87303678743/1000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((68743/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c63 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((369487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462031/2500000) (δ := 23/3125000) (ψ := -979041/1000000) 97 64
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t63 : ((232739077011/2500000000000 : ℚ) : ℝ) ≤ stT97 63 := by
  have hc : ((184731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232739077011/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((184731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c64 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-641187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5667101/10000000) (δ := 807/100000000) (ψ := -979041/1000000) 97 64
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t64 : ((-801546891237/10000000000000 : ℚ) : ℝ) ≤ stT97 64 := by
  have hc : ((-641237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-801546891237/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-641237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c65 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-404263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6281097/10000000) (δ := 339/50000000) (ψ := -979041/1000000) 97 65
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t65 : ((-1958819579/19531250000 : ℚ) : ℝ) ≤ stT97 65 := by
  have hc : ((-12634/15625 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1958819579/19531250000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-12634/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c66 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((513537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -515747/2000000) (δ := 113/20000000) (ψ := -979041/1000000) 97 65
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t66 : ((316029168559/5000000000000 : ℚ) : ℝ) ≤ stT97 66 := by
  have hc : ((513487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316029168559/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((513487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c67 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((455069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21359/200000) (δ := 159/20000000) (ψ := -979041/1000000) 97 65
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t67 : ((69490565567/625000000000 : ℚ) : ℝ) ≤ stT97 67 := by
  have hc : ((113761/125000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69490565567/625000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((113761/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c68 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-289253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36411/78125) (δ := 189/20000000) (ψ := -979041/1000000) 97 65
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t68 : ((-350831672737/10000000000000 : ℚ) : ℝ) ≤ stT97 68 := by
  have hc : ((-289303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350831672737/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-289303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c69 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-123799/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3753573/5000000) (δ := 467/50000000) (ψ := -979041/1000000) 97 66
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t69 : ((-596176257839/5000000000000 : ℚ) : ℝ) ≤ stT97 69 := by
  have hc : ((-495221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596176257839/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-495221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c70 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-18173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4017877/10000000) (δ := 141/25000000) (ψ := -979041/1000000) 97 66
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t70 : ((-10875388671/2500000000000 : ℚ) : ℝ) ≤ stT97 70 := by
  have hc : ((-9099/250000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10875388671/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-9099/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c71 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((973383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72263/1250000) (δ := 709/100000000) (ψ := -979041/1000000) 97 66
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t71 : ((1155133111073/10000000000000 : ℚ) : ℝ) ≤ stT97 71 := by
  have hc : ((973333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1155133111073/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((973333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c72 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((215397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70339/250000) (δ := 407/50000000) (ψ := -979041/1000000) 97 66
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t72 : ((63454567773/1250000000000 : ℚ) : ℝ) ≤ stT97 72 := by
  have hc : ((53843/125000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63454567773/1250000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((53843/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c73 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-778693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6158441/10000000) (δ := 73/12500000) (ψ := -979041/1000000) 97 66
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t73 : ((-227862538029/2500000000000 : ℚ) : ℝ) ≤ stT97 73 := by
  have hc : ((-778743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227862538029/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-778743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c74 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-40059/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781269/1250000) (δ := 11/1250000) (ψ := -979041/1000000) 97 67
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t74 : ((-93141144671/1000000000000 : ℚ) : ℝ) ≤ stT97 74 := by
  have hc : ((-80123/100000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93141144671/1000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-80123/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c75 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((72839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2995069/10000000) (δ := 843/100000000) (ψ := -979041/1000000) 97 67
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t75 : ((840956463/20000000000 : ℚ) : ℝ) ≤ stT97 75 := by
  have hc : ((72829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((840956463/20000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((72829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c76 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((996239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108449/5000000) (δ := 603/100000000) (ψ := -979041/1000000) 97 67
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t76 : ((571353242871/5000000000000 : ℚ) : ℝ) ≤ stT97 76 := by
  have hc : ((996189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571353242871/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((996189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c77 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((6699/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1693439/5000000) (δ := 773/100000000) (ψ := -979041/1000000) 97 67
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t77 : ((24423786439/1000000000000 : ℚ) : ℝ) ≤ stT97 77 := by
  have hc : ((107159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24423786439/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((107159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c78 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-860161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3257977/5000000) (δ := 713/100000000) (ψ := -979041/1000000) 97 67
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t78 : ((-486998995329/5000000000000 : ℚ) : ℝ) ≤ stT97 78 := by
  have hc : ((-860211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-486998995329/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-860211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c79 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-764537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1525699/2500000) (δ := 49/10000000) (ψ := -979041/1000000) 97 68
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t79 : ((-26882114333/312500000000 : ℚ) : ℝ) ≤ stT97 79 := by
  have hc : ((-764587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26882114333/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-764587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c80 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((342729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3052441/10000000) (δ := 643/100000000) (ψ := -979041/1000000) 97 68
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t80 : ((383126430407/10000000000000 : ℚ) : ℝ) ≤ stT97 80 := by
  have hc : ((342679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383126430407/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((342679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c81 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((15623/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1999/500000) (δ := 13/2500000) (ψ := -979041/1000000) 97 68
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t81 : ((555456611121/5000000000000 : ℚ) : ℝ) ≤ stT97 81 := by
  have hc : ((499911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((555456611121/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((499911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c82 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((15451/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2935517/10000000) (δ := 543/100000000) (ψ := -979041/1000000) 97 68
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t82 : ((3412112487/80000000000 : ℚ) : ℝ) ≤ stT97 82 := by
  have hc : ((15449/40000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3412112487/80000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((15449/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c83 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-351349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5874947/10000000) (δ := 923/100000000) (ψ := -979041/1000000) 97 68
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t83 : ((-192841605741/2500000000000 : ℚ) : ℝ) ≤ stT97 83 := by
  have hc : ((-175687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192841605741/2500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-175687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c84 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-9323/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692879/1000000) (δ := 253/25000000) (ψ := -979041/1000000) 97 69
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t84 : ((-2034555523/20000000000 : ℚ) : ℝ) ≤ stT97 84 := by
  have hc : ((-18647/20000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2034555523/20000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-18647/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c85 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-52753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2029467/5000000) (δ := 521/100000000) (ψ := -979041/1000000) 97 69
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t85 : ((-57272932359/10000000000000 : ℚ) : ℝ) ≤ stT97 85 := by
  have hc : ((-52803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57272932359/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-52803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c86 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((110347/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305661/2500000) (δ := 921/100000000) (ψ := -979041/1000000) 97 69
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t86 : ((475933639701/5000000000000 : ℚ) : ℝ) ≤ stT97 86 := by
  have hc : ((441363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475933639701/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((441363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c87 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((403323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316171/2000000) (δ := 411/50000000) (ψ := -979041/1000000) 97 69
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t87 : ((13511894543/156250000000 : ℚ) : ℝ) ≤ stT97 87 := by
  have hc : ((201649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13511894543/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((201649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c88 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-16931/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2176157/5000000) (δ := 213/25000000) (ψ := -979041/1000000) 97 69
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t88 : ((-564182617/31250000000 : ℚ) : ℝ) ≤ stT97 88 := by
  have hc : ((-2117/12500 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564182617/31250000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-2117/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c89 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-238491/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 886557/1250000) (δ := 651/100000000) (ψ := -979041/1000000) 97 69
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t89 : ((-252813232993/2500000000000 : ℚ) : ℝ) ≤ stT97 89 := by
  have hc : ((-477007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252813232993/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-477007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c90 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-177869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2952991/5000000) (δ := 163/25000000) (ψ := -979041/1000000) 97 70
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t90 : ((-375007287959/5000000000000 : ℚ) : ℝ) ≤ stT97 90 := by
  have hc : ((-355763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375007287959/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-355763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c91 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((34573/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -806599/2500000) (δ := 129/12500000) (ψ := -979041/1000000) 97 70
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t91 : ((36235770957/1250000000000 : ℚ) : ℝ) ≤ stT97 91 := by
  have hc : ((138267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36235770957/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((138267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c92 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((486783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -576097/10000000) (δ := 361/50000000) (ψ := -979041/1000000) 97 70
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t92 : ((63435032697/625000000000 : ℚ) : ℝ) ≤ stT97 92 := by
  have hc : ((243379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63435032697/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((243379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c93 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((341761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40911/200000) (δ := 109/12500000) (ψ := -979041/1000000) 97 70
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t93 : ((44295435867/625000000000 : ℚ) : ℝ) ≤ stT97 93 := by
  have hc : ((42717/62500 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44295435867/625000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((42717/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c94 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-28103/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2319579/5000000) (δ := 391/50000000) (ψ := -979041/1000000) 97 70
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t94 : ((-3623901197/125000000000 : ℚ) : ℝ) ≤ stT97 94 := by
  have hc : ((-7027/25000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3623901197/125000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-7027/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c95 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-966527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7205319/10000000) (δ := 213/25000000) (ψ := -979041/1000000) 97 70
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t95 : ((-991687703883/10000000000000 : ℚ) : ℝ) ≤ stT97 95 := by
  have hc : ((-966577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-991687703883/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-966577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c96 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-363707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2981677/5000000) (δ := 213/25000000) (ψ := -979041/1000000) 97 71
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t96 : ((-92808129393/1250000000000 : ℚ) : ℝ) ≤ stT97 96 := by
  have hc : ((-90933/125000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92808129393/1250000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-90933/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c97 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((47373/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1725189/5000000) (δ := 183/25000000) (ψ := -979041/1000000) 97 71
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t97 : ((48087294233/2500000000000 : ℚ) : ℝ) ≤ stT97 97 := by
  have hc : ((94721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48087294233/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((94721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c98 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((926697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120397/1250000) (δ := 381/50000000) (ψ := -979041/1000000) 97 71
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t98 : ((117006790043/1250000000000 : ℚ) : ℝ) ≤ stT97 98 := by
  have hc : ((926647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117006790043/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((926647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c99 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((206403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 749387/5000000) (δ := 491/100000000) (ψ := -979041/1000000) 97 71
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t99 : ((414860177897/5000000000000 : ℚ) : ℝ) ≤ stT97 99 := by
  have hc : ((412781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414860177897/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((412781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_c100 :
    |Real.cos (((97 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ))
      - ((-899/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196799/500000) (δ := 203/25000000) (ψ := -979041/1000000) 97 71
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st97_t100 : ((-1823/5000000 : ℚ) : ℝ) ≤ stT97 100 := by
  have hc : ((-1823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((97 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-979041/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st97_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1823/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-1823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st97_p1 : ((557769/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT97 (i+1) := by
  rw [Finset.sum_range_one]
  exact st97_t1

theorem st97_p2 : ((1993757450333/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT97 (i+1))
      = (∑ i ∈ Finset.range 1, stT97 (i+1)) + stT97 2 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 1
    simpa using h
  have hprev := st97_p1
  have hstep := st97_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p3 : ((14269676737537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT97 (i+1))
      = (∑ i ∈ Finset.range 2, stT97 (i+1)) + stT97 3 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 2
    simpa using h
  have hprev := st97_p2
  have hstep := st97_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p4 : ((4795950400991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT97 (i+1))
      = (∑ i ∈ Finset.range 3, stT97 (i+1)) + stT97 4 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 3
    simpa using h
  have hprev := st97_p3
  have hstep := st97_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p5 : ((14063315788247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT97 (i+1))
      = (∑ i ∈ Finset.range 4, stT97 (i+1)) + stT97 5 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 4
    simpa using h
  have hprev := st97_p4
  have hstep := st97_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p6 : ((15732695750313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT97 (i+1))
      = (∑ i ∈ Finset.range 5, stT97 (i+1)) + stT97 6 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 5
    simpa using h
  have hprev := st97_p5
  have hstep := st97_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p7 : ((3394334878489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT97 (i+1))
      = (∑ i ∈ Finset.range 6, stT97 (i+1)) + stT97 7 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 6
    simpa using h
  have hprev := st97_p6
  have hstep := st97_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p8 : ((3357445116733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT97 (i+1))
      = (∑ i ∈ Finset.range 7, stT97 (i+1)) + stT97 8 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 7
    simpa using h
  have hprev := st97_p7
  have hstep := st97_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p9 : ((3948271724317/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT97 (i+1))
      = (∑ i ∈ Finset.range 8, stT97 (i+1)) + stT97 9 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 8
    simpa using h
  have hprev := st97_p8
  have hstep := st97_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p10 : ((3764916521321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT97 (i+1))
      = (∑ i ∈ Finset.range 9, stT97 (i+1)) + stT97 10 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 9
    simpa using h
  have hprev := st97_p9
  have hstep := st97_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p11 : ((505001552041/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT97 (i+1))
      = (∑ i ∈ Finset.range 10, stT97 (i+1)) + stT97 11 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 10
    simpa using h
  have hprev := st97_p10
  have hstep := st97_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p12 : ((86656833577/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT97 (i+1))
      = (∑ i ∈ Finset.range 11, stT97 (i+1)) + stT97 12 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 11
    simpa using h
  have hprev := st97_p11
  have hstep := st97_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p13 : ((86968297627/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT97 (i+1))
      = (∑ i ∈ Finset.range 12, stT97 (i+1)) + stT97 13 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 12
    simpa using h
  have hprev := st97_p12
  have hstep := st97_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p14 : ((4883106324059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT97 (i+1))
      = (∑ i ∈ Finset.range 13, stT97 (i+1)) + stT97 14 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 13
    simpa using h
  have hprev := st97_p13
  have hstep := st97_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p15 : ((5510998038881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT97 (i+1))
      = (∑ i ∈ Finset.range 14, stT97 (i+1)) + stT97 15 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 14
    simpa using h
  have hprev := st97_p14
  have hstep := st97_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p16 : ((6115468038881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT97 (i+1))
      = (∑ i ∈ Finset.range 15, stT97 (i+1)) + stT97 16 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 15
    simpa using h
  have hprev := st97_p15
  have hstep := st97_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p17 : ((3297328572121/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT97 (i+1))
      = (∑ i ∈ Finset.range 16, stT97 (i+1)) + stT97 17 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 16
    simpa using h
  have hprev := st97_p16
  have hstep := st97_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p18 : ((6695805207839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT97 (i+1))
      = (∑ i ∈ Finset.range 17, stT97 (i+1)) + stT97 18 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 17
    simpa using h
  have hprev := st97_p17
  have hstep := st97_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p19 : ((625884725729/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT97 (i+1))
      = (∑ i ∈ Finset.range 18, stT97 (i+1)) + stT97 19 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 18
    simpa using h
  have hprev := st97_p18
  have hstep := st97_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p20 : ((1449601549259/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT97 (i+1))
      = (∑ i ∈ Finset.range 19, stT97 (i+1)) + stT97 20 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 19
    simpa using h
  have hprev := st97_p19
  have hstep := st97_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p21 : ((1524655379391/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT97 (i+1))
      = (∑ i ∈ Finset.range 20, stT97 (i+1)) + stT97 21 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 20
    simpa using h
  have hprev := st97_p20
  have hstep := st97_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p22 : ((5181188943363/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT97 (i+1))
      = (∑ i ∈ Finset.range 21, stT97 (i+1)) + stT97 22 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 21
    simpa using h
  have hprev := st97_p21
  have hstep := st97_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p23 : ((4795057621973/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT97 (i+1))
      = (∑ i ∈ Finset.range 22, stT97 (i+1)) + stT97 23 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 22
    simpa using h
  have hprev := st97_p22
  have hstep := st97_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p24 : ((4874788495433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT97 (i+1))
      = (∑ i ∈ Finset.range 23, stT97 (i+1)) + stT97 24 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 23
    simpa using h
  have hprev := st97_p23
  have hstep := st97_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p25 : ((5107679295433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT97 (i+1))
      = (∑ i ∈ Finset.range 24, stT97 (i+1)) + stT97 25 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 24
    simpa using h
  have hprev := st97_p24
  have hstep := st97_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p26 : ((23657049848241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT97 (i+1))
      = (∑ i ∈ Finset.range 25, stT97 (i+1)) + stT97 26 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 25
    simpa using h
  have hprev := st97_p25
  have hstep := st97_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p27 : ((25529553707241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT97 (i+1))
      = (∑ i ∈ Finset.range 26, stT97 (i+1)) + stT97 27 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 26
    simpa using h
  have hprev := st97_p26
  have hstep := st97_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p28 : ((11995047221163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT97 (i+1))
      = (∑ i ∈ Finset.range 27, stT97 (i+1)) + stT97 28 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 27
    simpa using h
  have hprev := st97_p27
  have hstep := st97_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p29 : ((5034317271887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT97 (i+1))
      = (∑ i ∈ Finset.range 28, stT97 (i+1)) + stT97 29 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 28
    simpa using h
  have hprev := st97_p28
  have hstep := st97_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p30 : ((24228375178879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT97 (i+1))
      = (∑ i ∈ Finset.range 29, stT97 (i+1)) + stT97 30 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 29
    simpa using h
  have hprev := st97_p29
  have hstep := st97_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p31 : ((12547685635599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT97 (i+1))
      = (∑ i ∈ Finset.range 30, stT97 (i+1)) + stT97 31 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 30
    simpa using h
  have hprev := st97_p30
  have hstep := st97_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p32 : ((1509226146843/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT97 (i+1))
      = (∑ i ∈ Finset.range 31, stT97 (i+1)) + stT97 32 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 31
    simpa using h
  have hprev := st97_p31
  have hstep := st97_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p33 : ((98822963387/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT97 (i+1))
      = (∑ i ∈ Finset.range 32, stT97 (i+1)) + stT97 33 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 32
    simpa using h
  have hprev := st97_p32
  have hstep := st97_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p34 : ((11942747074183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT97 (i+1))
      = (∑ i ∈ Finset.range 33, stT97 (i+1)) + stT97 34 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 33
    simpa using h
  have hprev := st97_p33
  have hstep := st97_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p35 : ((12756648124417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT97 (i+1))
      = (∑ i ∈ Finset.range 34, stT97 (i+1)) + stT97 35 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 34
    simpa using h
  have hprev := st97_p34
  have hstep := st97_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p36 : ((23862027585247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT97 (i+1))
      = (∑ i ∈ Finset.range 35, stT97 (i+1)) + stT97 36 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 35
    simpa using h
  have hprev := st97_p35
  have hstep := st97_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p37 : ((12599833727521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT97 (i+1))
      = (∑ i ∈ Finset.range 36, stT97 (i+1)) + stT97 37 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 36
    simpa using h
  have hprev := st97_p36
  have hstep := st97_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p38 : ((24574259772737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT97 (i+1))
      = (∑ i ∈ Finset.range 37, stT97 (i+1)) + stT97 38 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 37
    simpa using h
  have hprev := st97_p37
  have hstep := st97_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p39 : ((24214980130397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT97 (i+1))
      = (∑ i ∈ Finset.range 38, stT97 (i+1)) + stT97 39 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 38
    simpa using h
  have hprev := st97_p38
  have hstep := st97_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p40 : ((5093032762213/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT97 (i+1))
      = (∑ i ∈ Finset.range 39, stT97 (i+1)) + stT97 40 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 39
    simpa using h
  have hprev := st97_p39
  have hstep := st97_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p41 : ((23909340112871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT97 (i+1))
      = (∑ i ∈ Finset.range 40, stT97 (i+1)) + stT97 41 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 40
    simpa using h
  have hprev := st97_p40
  have hstep := st97_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p42 : ((4975672350161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT97 (i+1))
      = (∑ i ∈ Finset.range 41, stT97 (i+1)) + stT97 42 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 41
    simpa using h
  have hprev := st97_p41
  have hstep := st97_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p43 : ((5030288162951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT97 (i+1))
      = (∑ i ∈ Finset.range 42, stT97 (i+1)) + stT97 43 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 42
    simpa using h
  have hprev := st97_p42
  have hstep := st97_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p44 : ((372086558701/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT97 (i+1))
      = (∑ i ∈ Finset.range 43, stT97 (i+1)) + stT97 44 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 43
    simpa using h
  have hprev := st97_p43
  have hstep := st97_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p45 : ((25133902738761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT97 (i+1))
      = (∑ i ∈ Finset.range 44, stT97 (i+1)) + stT97 45 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 44
    simpa using h
  have hprev := st97_p44
  have hstep := st97_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p46 : ((25018166666441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT97 (i+1))
      = (∑ i ∈ Finset.range 45, stT97 (i+1)) + stT97 46 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 45
    simpa using h
  have hprev := st97_p45
  have hstep := st97_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p47 : ((23809161696641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT97 (i+1))
      = (∑ i ∈ Finset.range 46, stT97 (i+1)) + stT97 47 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 46
    simpa using h
  have hprev := st97_p46
  have hstep := st97_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p48 : ((25071889655141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT97 (i+1))
      = (∑ i ∈ Finset.range 47, stT97 (i+1)) + stT97 48 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 47
    simpa using h
  have hprev := st97_p47
  have hstep := st97_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p49 : ((6295179905623/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT97 (i+1))
      = (∑ i ∈ Finset.range 48, stT97 (i+1)) + stT97 49 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 48
    simpa using h
  have hprev := st97_p48
  have hstep := st97_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p50 : ((11917477497153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT97 (i+1))
      = (∑ i ∈ Finset.range 49, stT97 (i+1)) + stT97 50 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 49
    simpa using h
  have hprev := st97_p49
  have hstep := st97_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p51 : ((12348157415913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT97 (i+1))
      = (∑ i ∈ Finset.range 50, stT97 (i+1)) + stT97 51 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 50
    simpa using h
  have hprev := st97_p50
  have hstep := st97_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p52 : ((3184251395697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT97 (i+1))
      = (∑ i ∈ Finset.range 51, stT97 (i+1)) + stT97 52 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 51
    simpa using h
  have hprev := st97_p51
  have hstep := st97_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p53 : ((3021179638589/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT97 (i+1))
      = (∑ i ∈ Finset.range 52, stT97 (i+1)) + stT97 53 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 52
    simpa using h
  have hprev := st97_p52
  have hstep := st97_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p54 : ((3008221834373/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT97 (i+1))
      = (∑ i ∈ Finset.range 53, stT97 (i+1)) + stT97 54 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 53
    simpa using h
  have hprev := st97_p53
  have hstep := st97_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p55 : ((3175277683281/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT97 (i+1))
      = (∑ i ∈ Finset.range 54, stT97 (i+1)) + stT97 55 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 54
    simpa using h
  have hprev := st97_p54
  have hstep := st97_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p56 : ((9763542661/3906250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT97 (i+1))
      = (∑ i ∈ Finset.range 55, stT97 (i+1)) + stT97 56 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 55
    simpa using h
  have hprev := st97_p55
  have hstep := st97_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p57 : ((23805369706927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT97 (i+1))
      = (∑ i ∈ Finset.range 56, stT97 (i+1)) + stT97 57 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 56
    simpa using h
  have hprev := st97_p56
  have hstep := st97_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p58 : ((24516233669119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT97 (i+1))
      = (∑ i ∈ Finset.range 57, stT97 (i+1)) + stT97 58 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 57
    simpa using h
  have hprev := st97_p57
  have hstep := st97_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p59 : ((25545051451369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT97 (i+1))
      = (∑ i ∈ Finset.range 58, stT97 (i+1)) + stT97 59 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 58
    simpa using h
  have hprev := st97_p58
  have hstep := st97_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p60 : ((12347351368877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT97 (i+1))
      = (∑ i ∈ Finset.range 59, stT97 (i+1)) + stT97 60 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 59
    simpa using h
  have hprev := st97_p59
  have hstep := st97_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p61 : ((23759151193513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT97 (i+1))
      = (∑ i ∈ Finset.range 60, stT97 (i+1)) + stT97 61 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 60
    simpa using h
  have hprev := st97_p60
  have hstep := st97_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p62 : ((24632187980943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT97 (i+1))
      = (∑ i ∈ Finset.range 61, stT97 (i+1)) + stT97 62 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 61
    simpa using h
  have hprev := st97_p61
  have hstep := st97_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p63 : ((25563144288987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT97 (i+1))
      = (∑ i ∈ Finset.range 62, stT97 (i+1)) + stT97 63 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 62
    simpa using h
  have hprev := st97_p62
  have hstep := st97_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p64 : ((99046389591/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT97 (i+1))
      = (∑ i ∈ Finset.range 63, stT97 (i+1)) + stT97 64 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 63
    simpa using h
  have hprev := st97_p63
  have hstep := st97_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p65 : ((11879340886651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT97 (i+1))
      = (∑ i ∈ Finset.range 64, stT97 (i+1)) + stT97 65 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 64
    simpa using h
  have hprev := st97_p64
  have hstep := st97_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p66 : ((1219537005521/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT97 (i+1))
      = (∑ i ∈ Finset.range 65, stT97 (i+1)) + stT97 66 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 65
    simpa using h
  have hprev := st97_p65
  have hstep := st97_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p67 : ((6375647289873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT97 (i+1))
      = (∑ i ∈ Finset.range 66, stT97 (i+1)) + stT97 67 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 66
    simpa using h
  have hprev := st97_p66
  have hstep := st97_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p68 : ((5030351497351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT97 (i+1))
      = (∑ i ∈ Finset.range 67, stT97 (i+1)) + stT97 68 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 67
    simpa using h
  have hprev := st97_p67
  have hstep := st97_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p69 : ((23959404971077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT97 (i+1))
      = (∑ i ∈ Finset.range 68, stT97 (i+1)) + stT97 69 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 68
    simpa using h
  have hprev := st97_p68
  have hstep := st97_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p70 : ((23915903416393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT97 (i+1))
      = (∑ i ∈ Finset.range 69, stT97 (i+1)) + stT97 70 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 69
    simpa using h
  have hprev := st97_p69
  have hstep := st97_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p71 : ((12535518263733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT97 (i+1))
      = (∑ i ∈ Finset.range 70, stT97 (i+1)) + stT97 71 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 70
    simpa using h
  have hprev := st97_p70
  have hstep := st97_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p72 : ((511573461393/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT97 (i+1))
      = (∑ i ∈ Finset.range 71, stT97 (i+1)) + stT97 72 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 71
    simpa using h
  have hprev := st97_p71
  have hstep := st97_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p73 : ((12333611458767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT97 (i+1))
      = (∑ i ∈ Finset.range 72, stT97 (i+1)) + stT97 73 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 72
    simpa using h
  have hprev := st97_p72
  have hstep := st97_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p74 : ((2966976433853/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT97 (i+1))
      = (∑ i ∈ Finset.range 73, stT97 (i+1)) + stT97 74 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 73
    simpa using h
  have hprev := st97_p73
  have hstep := st97_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p75 : ((6039072425581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT97 (i+1))
      = (∑ i ∈ Finset.range 74, stT97 (i+1)) + stT97 75 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 74
    simpa using h
  have hprev := st97_p74
  have hstep := st97_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p76 : ((12649498094033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT97 (i+1))
      = (∑ i ∈ Finset.range 75, stT97 (i+1)) + stT97 76 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 75
    simpa using h
  have hprev := st97_p75
  have hstep := st97_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p77 : ((3192904256557/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT97 (i+1))
      = (∑ i ∈ Finset.range 76, stT97 (i+1)) + stT97 77 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 76
    simpa using h
  have hprev := st97_p76
  have hstep := st97_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p78 : ((12284618030899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT97 (i+1))
      = (∑ i ∈ Finset.range 77, stT97 (i+1)) + stT97 78 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 77
    simpa using h
  have hprev := st97_p77
  have hstep := st97_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p79 : ((11854504201571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT97 (i+1))
      = (∑ i ∈ Finset.range 78, stT97 (i+1)) + stT97 79 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 78
    simpa using h
  have hprev := st97_p78
  have hstep := st97_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p80 : ((24092134833549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT97 (i+1))
      = (∑ i ∈ Finset.range 79, stT97 (i+1)) + stT97 80 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 79
    simpa using h
  have hprev := st97_p79
  have hstep := st97_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p81 : ((25203048055791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT97 (i+1))
      = (∑ i ∈ Finset.range 80, stT97 (i+1)) + stT97 81 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 80
    simpa using h
  have hprev := st97_p80
  have hstep := st97_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p82 : ((12814781058333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT97 (i+1))
      = (∑ i ∈ Finset.range 81, stT97 (i+1)) + stT97 82 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 81
    simpa using h
  have hprev := st97_p81
  have hstep := st97_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p83 : ((12429097846851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT97 (i+1))
      = (∑ i ∈ Finset.range 82, stT97 (i+1)) + stT97 83 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 82
    simpa using h
  have hprev := st97_p82
  have hstep := st97_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p84 : ((11920458966101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT97 (i+1))
      = (∑ i ∈ Finset.range 83, stT97 (i+1)) + stT97 84 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 83
    simpa using h
  have hprev := st97_p83
  have hstep := st97_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p85 : ((23783644999843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT97 (i+1))
      = (∑ i ∈ Finset.range 84, stT97 (i+1)) + stT97 85 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 84
    simpa using h
  have hprev := st97_p84
  have hstep := st97_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p86 : ((4947102455849/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT97 (i+1))
      = (∑ i ∈ Finset.range 85, stT97 (i+1)) + stT97 86 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 85
    simpa using h
  have hprev := st97_p85
  have hstep := st97_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p87 : ((25600273529997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT97 (i+1))
      = (∑ i ∈ Finset.range 86, stT97 (i+1)) + stT97 87 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 86
    simpa using h
  have hprev := st97_p86
  have hstep := st97_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p88 : ((25419735092557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT97 (i+1))
      = (∑ i ∈ Finset.range 87, stT97 (i+1)) + stT97 88 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 87
    simpa using h
  have hprev := st97_p87
  have hstep := st97_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p89 : ((4881696432117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT97 (i+1))
      = (∑ i ∈ Finset.range 88, stT97 (i+1)) + stT97 89 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 88
    simpa using h
  have hprev := st97_p88
  have hstep := st97_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p90 : ((23658467584667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT97 (i+1))
      = (∑ i ∈ Finset.range 89, stT97 (i+1)) + stT97 90 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 89
    simpa using h
  have hprev := st97_p89
  have hstep := st97_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p91 : ((23948353752323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT97 (i+1))
      = (∑ i ∈ Finset.range 90, stT97 (i+1)) + stT97 91 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 90
    simpa using h
  have hprev := st97_p90
  have hstep := st97_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p92 : ((998532571019/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT97 (i+1))
      = (∑ i ∈ Finset.range 91, stT97 (i+1)) + stT97 92 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 91
    simpa using h
  have hprev := st97_p91
  have hstep := st97_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p93 : ((25672041249347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT97 (i+1))
      = (∑ i ∈ Finset.range 92, stT97 (i+1)) + stT97 93 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 92
    simpa using h
  have hprev := st97_p92
  have hstep := st97_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p94 : ((25382129153587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT97 (i+1))
      = (∑ i ∈ Finset.range 93, stT97 (i+1)) + stT97 94 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 93
    simpa using h
  have hprev := st97_p93
  have hstep := st97_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p95 : ((3048805181213/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT97 (i+1))
      = (∑ i ∈ Finset.range 94, stT97 (i+1)) + stT97 95 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 94
    simpa using h
  have hprev := st97_p94
  have hstep := st97_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p96 : ((147799852591/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT97 (i+1))
      = (∑ i ∈ Finset.range 95, stT97 (i+1)) + stT97 96 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 95
    simpa using h
  have hprev := st97_p95
  have hstep := st97_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p97 : ((5960081397873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT97 (i+1))
      = (∑ i ∈ Finset.range 96, stT97 (i+1)) + stT97 97 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 96
    simpa using h
  have hprev := st97_p96
  have hstep := st97_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p98 : ((6194094977959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT97 (i+1))
      = (∑ i ∈ Finset.range 97, stT97 (i+1)) + stT97 98 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 97
    simpa using h
  have hprev := st97_p97
  have hstep := st97_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p99 : ((2560610026763/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT97 (i+1))
      = (∑ i ∈ Finset.range 98, stT97 (i+1)) + stT97 99 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 98
    simpa using h
  have hprev := st97_p98
  have hstep := st97_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st97_p100 : ((2560245426763/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT97 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT97 (i+1))
      = (∑ i ∈ Finset.range 99, stT97 (i+1)) + stT97 100 := by
    have h := Finset.sum_range_succ (fun i => stT97 (i+1)) 99
    simpa using h
  have hprev := st97_p99
  have hstep := st97_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 97`.** -/
theorem station_97_sign : hardyG (((97:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 97 100 (by norm_num) (by norm_num)
    ((-979041/1000000 : ℚ) : ℝ)
  have hchain := st97_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT97 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((97:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-979041/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((97:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((97:ℕ)):ℝ)+1) * ((((97:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((37780347/38800000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2560245426763/1000000000000 : ℚ) : ℝ) - ((37780347/38800000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-979041/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((97:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-979041/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((97:ℕ)):ℝ))).re
      - Real.sin ((-979041/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((97:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((97:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((97:ℕ)):ℝ)
      = ((((97:ℕ)):ℝ) * (Real.log (((97:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((97:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_97
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
  have hθwin : |(((-979041/1000000 : ℚ) : ℝ) + ((14:ℤ)) * (2*Real.pi) - Real.pi) - theta (((97:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((97:ℕ)):ℝ))
    (φ := ((-979041/1000000 : ℚ) : ℝ) + ((14:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-979041/1000000 : ℚ) : ℝ) + ((14:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-979041/1000000 : ℚ)) : ℝ) - Real.pi) + ((14:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-979041/1000000 : ℚ)) : ℝ) - Real.pi) 14).1,
    (cos_sin_shift ((((-979041/1000000 : ℚ)) : ℝ) - Real.pi) 14).2]
  exact cos_sin_flip ((-979041/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_97_sign
end AxiomAudit
