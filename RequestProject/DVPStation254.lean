import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 254` (rung-262.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT254 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((254 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((563/31250 : ℚ) : ℝ))

theorem st254_c1 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((499919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -563/125000) (δ := 1/1000000000) (ψ := 563/31250) 254 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t1 : ((249947/250000 : ℚ) : ℝ) ≤ stT254 1 := by
  have hc : ((249947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249947/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((249947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c2 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((198743/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 280429/10000000) (δ := 12803/1000000000) (ψ := 563/31250) 254 28
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t2 : ((1405254358111/2000000000000 : ℚ) : ℝ) ≤ stT254 2 := by
  have hc : ((198733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1405254358111/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((198733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c3 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-210171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1284671/2000000) (δ := 12717/1000000000) (ψ := 563/31250) 254 44
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t3 : ((-2426990135601/5000000000000 : ℚ) : ℝ) ≤ stT254 3 := by
  have hc : ((-420367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2426990135601/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-420367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c4 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((242693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 605929/10000000) (δ := 12799/1000000000) (ψ := 563/31250) 254 56
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t4 : ((485361/1000000 : ℚ) : ℝ) ≤ stT254 4 := by
  have hc : ((485361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((485361/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((485361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c5 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((931537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465223/5000000) (δ := 399/31250000) (ψ := 563/31250) 254 65
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t5 : ((833147122949/2000000000000 : ℚ) : ℝ) ≤ stT254 5 := by
  have hc : ((931487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((833147122949/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((931487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c6 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-225969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1349771/2000000) (δ := 2577/200000000) (ψ := 563/31250) 254 72
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t6 : ((-1845131264129/5000000000000 : ℚ) : ℝ) ≤ stT254 6 := by
  have hc : ((-451963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1845131264129/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-451963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c7 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-26461/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5321193/10000000) (δ := 6367/500000000) (ψ := 563/31250) 254 79
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t7 : ((-40009054183/200000000000 : ℚ) : ℝ) ≤ stT254 7 := by
  have hc : ((-52927/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40009054183/200000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-52927/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c8 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((465697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93143/1000000) (δ := 2561/200000000) (ψ := 563/31250) 254 84
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t8 : ((205799840397/625000000000 : ℚ) : ℝ) ≤ stT254 8 := by
  have hc : ((58209/62500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205799840397/625000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((58209/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c9 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((429847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1408091/5000000) (δ := 12863/1000000000) (ψ := 563/31250) 254 89
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t9 : ((1432656523401/10000000000000 : ℚ) : ℝ) ≤ stT254 9 := by
  have hc : ((429797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1432656523401/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((429797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c10 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((219113/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1255883/10000000) (δ := 12769/1000000000) (ψ := 563/31250) 254 93
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t10 : ((1385712943677/5000000000000 : ℚ) : ℝ) ≤ stT254 10 := by
  have hc : ((438201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1385712943677/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((438201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c11 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((912437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053993/10000000) (δ := 6399/500000000) (ψ := 563/31250) 254 97
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t11 : ((2750949904731/10000000000000 : ℚ) : ℝ) ≤ stT254 11 := by
  have hc : ((912387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2750949904731/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((912387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c12 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-118971/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1768589/2500000) (δ := 12719/1000000000) (ψ := 563/31250) 254 100
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t12 : ((-42932226799/156250000000 : ℚ) : ℝ) ≤ stT254 12 := by
  have hc : ((-475909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42932226799/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-475909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c13 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-97667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4930383/10000000) (δ := 2571/200000000) (ψ := 563/31250) 254 104
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t13 : ((-541828381859/5000000000000 : ℚ) : ℝ) ≤ stT254 13 := by
  have hc : ((-195359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-541828381859/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-195359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c14 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-414579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1248923/2500000) (δ := 1287/100000000) (ψ := 563/31250) 254 107
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t14 : ((-1108142855577/10000000000000 : ℚ) : ℝ) ≤ stT254 14 := by
  have hc : ((-414629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1108142855577/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-414629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c15 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-245869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7398873/10000000) (δ := 3221/250000000) (ψ := 563/31250) 254 109
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t15 : ((-1269726656607/5000000000000 : ℚ) : ℝ) ≤ stT254 15 := by
  have hc : ((-491763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1269726656607/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-491763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c16 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((701/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125693/1000000) (δ := 12797/1000000000) (ψ := 563/31250) 254 112
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t16 : ((4381/20000 : ℚ) : ℝ) ≤ stT254 16 := by
  have hc : ((4381/5000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4381/20000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((4381/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c17 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-196269/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7370339/10000000) (δ := 3219/250000000) (ψ := 563/31250) 254 115
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t17 : ((-476046646603/2000000000000 : ℚ) : ℝ) ≤ stT254 17 := by
  have hc : ((-196279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-476046646603/2000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-196279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c18 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((108687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2490681/10000000) (δ := 6371/500000000) (ψ := 563/31250) 254 117
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t18 : ((128077039947/1000000000000 : ℚ) : ℝ) ≤ stT254 18 := by
  have hc : ((108677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128077039947/1000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((108677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c19 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((985513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26629/625000) (δ := 12847/1000000000) (ψ := 563/31250) 254 119
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t19 : ((2260806839691/10000000000000 : ℚ) : ℝ) ≤ stT254 19 := by
  have hc : ((985463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2260806839691/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((985463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c20 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((806521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1581383/10000000) (δ := 12833/1000000000) (ψ := 563/31250) 254 121
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t20 : ((1803323189557/10000000000000 : ℚ) : ℝ) ≤ stT254 20 := by
  have hc : ((806471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1803323189557/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((806471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c21 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((896543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 573617/5000000) (δ := 2557/200000000) (ψ := 563/31250) 254 123
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t21 : ((978153650877/5000000000000 : ℚ) : ℝ) ≤ stT254 21 := by
  have hc : ((896493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((978153650877/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((896493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c22 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((957843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -728493/10000000) (δ := 3201/250000000) (ψ := 563/31250) 254 125
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t22 : ((2042021380551/10000000000000 : ℚ) : ℝ) ≤ stT254 22 := by
  have hc : ((957793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2042021380551/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((957793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c23 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((1893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1958763/5000000) (δ := 12813/1000000000) (ψ := 563/31250) 254 127
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t23 : ((121720281/156250000000 : ℚ) : ℝ) ≤ stT254 23 := by
  have hc : ((467/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121720281/156250000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((467/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c24 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-983547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462491/625000) (δ := 12883/1000000000) (ψ := 563/31250) 254 128
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t24 : ((-1003879753737/5000000000000 : ℚ) : ℝ) ≤ stT254 24 := by
  have hc : ((-983597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1003879753737/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-983597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c25 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((90401/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19059/100000) (δ := 2547/200000000) (ψ := 563/31250) 254 130
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t25 : ((361579/2500000 : ℚ) : ℝ) ≤ stT254 25 := by
  have hc : ((361579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361579/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((361579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c26 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-133923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2302441/5000000) (δ := 12749/1000000000) (ψ := 563/31250) 254 132
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t26 : ((-32836715947/625000000000 : ℚ) : ℝ) ≤ stT254 26 := by
  have hc : ((-33487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32836715947/625000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-33487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c27 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((109677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 730449/2000000) (δ := 12747/1000000000) (ψ := 563/31250) 254 133
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t27 : ((421954323/20000000000 : ℚ) : ℝ) ≤ stT254 27 := by
  have hc : ((109627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421954323/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((109627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c28 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-292921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -291887/625000) (δ := 3183/250000000) (ψ := 563/31250) 254 135
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t28 : ((-553663334133/10000000000000 : ℚ) : ℝ) ≤ stT254 28 := by
  have hc : ((-292971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553663334133/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-292971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c29 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((361753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95241/500000) (δ := 513/40000000) (ψ := 563/31250) 254 136
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t29 : ((2623874589/19531250000 : ℚ) : ℝ) ≤ stT254 29 := by
  have hc : ((11304/15625 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2623874589/19531250000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((11304/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c30 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-199731/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 772431/1000000) (δ := 2577/200000000) (ψ := 563/31250) 254 137
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t30 : ((-182337766411/1000000000000 : ℚ) : ℝ) ≤ stT254 30 := by
  have hc : ((-199741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182337766411/1000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-199741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c31 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((410301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287003/1000000) (δ := 12899/1000000000) (ψ := 563/31250) 254 139
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t31 : ((736832539303/10000000000000 : ℚ) : ℝ) ≤ stT254 31 := by
  have hc : ((410251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((736832539303/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((410251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c32 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((806273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1582431/10000000) (δ := 12807/1000000000) (ψ := 563/31250) 254 140
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t32 : ((712606803909/5000000000000 : ℚ) : ℝ) ≤ stT254 32 := by
  have hc : ((806223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((712606803909/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((806223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c33 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-56049/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5414433/10000000) (δ := 12889/1000000000) (ψ := 563/31250) 254 141
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t33 : ((-48788756979/500000000000 : ℚ) : ℝ) ≤ stT254 33 := by
  have hc : ((-28027/50000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48788756979/500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-28027/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c34 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-948079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3522419/5000000) (δ := 1591/125000000) (ψ := 563/31250) 254 143
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t34 : ((-813013980597/5000000000000 : ℚ) : ℝ) ≤ stT254 34 := by
  have hc : ((-948129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-813013980597/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-948129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c35 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-166717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4345739/10000000) (δ := 399/31250000) (ψ := 563/31250) 254 144
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t35 : ((-281887761003/10000000000000 : ℚ) : ℝ) ≤ stT254 35 := by
  have hc : ((-166767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281887761003/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-166767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c36 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((40489/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2165181/10000000) (δ := 643/50000000) (ψ := 563/31250) 254 145
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t36 : ((269905725371/2500000000000 : ℚ) : ℝ) ≤ stT254 36 := by
  have hc : ((323887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269905725371/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((323887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c37 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((982021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -474779/10000000) (δ := 12753/1000000000) (ψ := 563/31250) 254 146
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t37 : ((1614349522319/10000000000000 : ℚ) : ℝ) ≤ stT254 37 := by
  have hc : ((981971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1614349522319/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((981971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c38 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((955151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150313/2000000) (δ := 12757/1000000000) (ψ := 563/31250) 254 147
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t38 : ((774689106807/5000000000000 : ℚ) : ℝ) ≤ stT254 38 := by
  have hc : ((955101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((774689106807/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((955101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c39 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((102081/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 384511/2500000) (δ := 12739/1000000000) (ψ := 563/31250) 254 148
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t39 : ((653801431019/5000000000000 : ℚ) : ℝ) ≤ stT254 39 := by
  have hc : ((408299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((653801431019/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((408299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c40 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((90367/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 476721/2500000) (δ := 12771/1000000000) (ψ := 563/31250) 254 149
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t40 : ((285745631067/2500000000000 : ℚ) : ℝ) ≤ stT254 40 := by
  have hc : ((361443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285745631067/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((361443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c41 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((730673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 939361/5000000) (δ := 6439/500000000) (ψ := 563/31250) 254 150
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t41 : ((1141040972151/10000000000000 : ℚ) : ℝ) ≤ stT254 41 := by
  have hc : ((730623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1141040972151/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((730623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c42 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((166289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 736367/5000000) (δ := 12817/1000000000) (ψ := 563/31250) 254 151
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t42 : ((256573984207/2000000000000 : ℚ) : ℝ) ≤ stT254 42 := by
  have hc : ((166279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256573984207/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((166279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c43 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((480159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 706639/10000000) (δ := 12893/1000000000) (ψ := 563/31250) 254 152
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t43 : ((73219714799/500000000000 : ℚ) : ℝ) ≤ stT254 43 := by
  have hc : ((240067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73219714799/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((240067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c44 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((246759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25187/625000) (δ := 1/78125) (ψ := 563/31250) 254 153
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t44 : ((185992083277/1250000000000 : ℚ) : ℝ) ≤ stT254 44 := by
  have hc : ((493493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185992083277/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((493493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c45 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((185241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -230091/1250000) (δ := 403/31250000) (ψ := 563/31250) 254 154
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t45 : ((552244324927/5000000000000 : ℚ) : ℝ) ≤ stT254 45 := by
  have hc : ((370457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((552244324927/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((370457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c46 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((3339/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3592089/10000000) (δ := 6407/500000000) (ψ := 563/31250) 254 155
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t46 : ((19684968069/1000000000000 : ℚ) : ℝ) ≤ stT254 46 := by
  have hc : ((13351/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19684968069/1000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((13351/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c47 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-63393/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176361/312500) (δ := 6361/500000000) (ψ := 563/31250) 254 156
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t47 : ((-924754927/10000000000 : ℚ) : ℝ) ≤ stT254 47 := by
  have hc : ((-31699/50000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-924754927/10000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-31699/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c48 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-998677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7725357/10000000) (δ := 6361/500000000) (ψ := 563/31250) 254 156
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t48 : ((-90096161397/625000000000 : ℚ) : ℝ) ≤ stT254 48 := by
  have hc : ((-998727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90096161397/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-998727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c49 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-455949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2555293/5000000) (δ := 12829/1000000000) (ψ := 563/31250) 254 157
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t49 : ((-162856850857/2500000000000 : ℚ) : ℝ) ≤ stT254 49 := by
  have hc : ((-455999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162856850857/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-455999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c50 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((627421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11157/50000) (δ := 12867/1000000000) (ψ := 563/31250) 254 158
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t50 : ((887236224023/10000000000000 : ℚ) : ℝ) ≤ stT254 50 := by
  have hc : ((627371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((887236224023/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((627371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c51 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((935627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112739/1250000) (δ := 319/25000000) (ψ := 563/31250) 254 159
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t51 : ((32751744039/250000000000 : ℚ) : ℝ) ≤ stT254 51 := by
  have hc : ((935577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32751744039/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((935577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c52 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-14049/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2139691/5000000) (δ := 12853/1000000000) (ψ := 563/31250) 254 160
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t52 : ((-9744699277/500000000000 : ℚ) : ℝ) ≤ stT254 52 := by
  have hc : ((-7027/50000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9744699277/500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-7027/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c53 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-499943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312649/400000) (δ := 12853/1000000000) (ψ := 563/31250) 254 160
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t53 : ((-1341326259/9765625000 : ℚ) : ℝ) ≤ stT254 53 := by
  have hc : ((-15624/15625 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1341326259/9765625000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-15624/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c54 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-20301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1988873/5000000) (δ := 12857/1000000000) (ψ := 563/31250) 254 161
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t54 : ((-6923552657/2500000000000 : ℚ) : ℝ) ≤ stT254 54 := by
  have hc : ((-20351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6923552657/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-20351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c55 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((999507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78539/10000000) (δ := 2553/200000000) (ψ := 563/31250) 254 162
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t55 : ((1347666819343/10000000000000 : ℚ) : ℝ) ≤ stT254 55 := by
  have hc : ((999457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1347666819343/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((999457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c56 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-166329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -868951/2000000) (δ := 12731/1000000000) (ψ := 563/31250) 254 163
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t56 : ((-222333422353/10000000000000 : ℚ) : ℝ) ≤ stT254 56 := by
  have hc : ((-166379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222333422353/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-166379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c57 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-3709/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6894491/10000000) (δ := 12731/1000000000) (ψ := 563/31250) 254 163
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t57 : ((-12282394509/100000000000 : ℚ) : ℝ) ≤ stT254 57 := by
  have hc : ((-9273/10000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12282394509/100000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-9273/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c58 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((627757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2230321/10000000) (δ := 12779/1000000000) (ψ := 563/31250) 254 164
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t58 : ((103027433031/1250000000000 : ℚ) : ℝ) ≤ stT254 58 := by
  have hc : ((627707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103027433031/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((627707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c59 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((49837/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1311349/5000000) (δ := 6443/500000000) (ψ := 563/31250) 254 165
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t59 : ((8109466581/125000000000 : ℚ) : ℝ) ≤ stT254 59 := by
  have hc : ((6229/12500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8109466581/125000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((6229/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c60 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-498467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7658153/10000000) (δ := 12793/1000000000) (ψ := 563/31250) 254 166
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t60 : ((-32177533977/250000000000 : ℚ) : ℝ) ≤ stT254 60 := by
  have hc : ((-124623/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32177533977/250000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-124623/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c61 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((421969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44343/156250) (δ := 1281/100000000) (ψ := 563/31250) 254 166
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t61 : ((33763224137/625000000000 : ℚ) : ℝ) ≤ stT254 61 := by
  have hc : ((421919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33763224137/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((421919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c62 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((65651/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2544593/10000000) (δ := 129/10000000) (ψ := 563/31250) 254 167
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t62 : ((333475592579/5000000000000 : ℚ) : ℝ) ≤ stT254 62 := by
  have hc : ((262579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333475592579/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((262579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c63 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-49773/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7615661/10000000) (δ := 129/10000000) (ψ := 563/31250) 254 167
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t63 : ((-62711256491/500000000000 : ℚ) : ℝ) ≤ stT254 63 := by
  have hc : ((-99551/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62711256491/500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-99551/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c64 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((90333/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 476967/2500000) (δ := 1601/125000000) (ψ := 563/31250) 254 168
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t64 : ((361307/4000000 : ℚ) : ℝ) ≤ stT254 64 := by
  have hc : ((361307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361307/4000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((361307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c65 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-447/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3954929/10000000) (δ := 1611/125000000) (ψ := 563/31250) 254 169
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t65 : ((-139229063/100000000000 : ℚ) : ℝ) ≤ stT254 65 := by
  have hc : ((-449/40000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139229063/100000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-449/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c66 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-165817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2869967/5000000) (δ := 2543/200000000) (ψ := 563/31250) 254 169
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t66 : ((-81648807597/1000000000000 : ℚ) : ℝ) ≤ stT254 66 := by
  have hc : ((-331659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81648807597/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-331659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c67 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((98599/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418963/10000000) (δ := 12781/1000000000) (ψ := 563/31250) 254 170
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t67 : ((30112924559/250000000000 : ℚ) : ℝ) ≤ stT254 67 := by
  have hc : ((49297/50000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30112924559/250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((49297/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c68 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-898763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3359669/5000000) (δ := 6437/500000000) (ψ := 563/31250) 254 171
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t68 : ((-1089971650027/10000000000000 : ℚ) : ℝ) ≤ stT254 68 := by
  have hc : ((-898813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1089971650027/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-898813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c69 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((523059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25509/100000) (δ := 6437/500000000) (ψ := 563/31250) 254 171
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t69 : ((314814284361/5000000000000 : ℚ) : ℝ) ≤ stT254 69 := by
  have hc : ((523009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((314814284361/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((523009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c70 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-3729/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2010119/5000000) (δ := 3209/250000000) (ψ := 563/31250) 254 172
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t70 : ((-2231492543/500000000000 : ℚ) : ℝ) ≤ stT254 70 := by
  have hc : ((-1867/50000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2231492543/500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-1867/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c71 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-411407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4986983/10000000) (δ := 3209/250000000) (ψ := 563/31250) 254 172
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t71 : ((-244154880687/5000000000000 : ℚ) : ℝ) ≤ stT254 71 := by
  have hc : ((-411457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244154880687/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-411457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c72 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((370623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5749/31250) (δ := 1593/125000000) (ψ := 563/31250) 254 173
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t72 : ((218376909789/2500000000000 : ℚ) : ℝ) ≤ stT254 72 := by
  have hc : ((185299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218376909789/2500000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((185299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c73 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-465443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1383813/2000000) (δ := 12859/1000000000) (ψ := 563/31250) 254 173
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t73 : ((-34049333301/312500000000 : ℚ) : ℝ) ≤ stT254 73 := by
  have hc : ((-116367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34049333301/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-116367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c74 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((124777/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74671/5000000) (δ := 797/62500000) (ψ := 563/31250) 254 174
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t74 : ((145043002377/1250000000000 : ℚ) : ℝ) ≤ stT254 74 := by
  have hc : ((499083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145043002377/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((499083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c75 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-978417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7333637/10000000) (δ := 2569/200000000) (ψ := 563/31250) 254 175
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t75 : ((-1129836823367/10000000000000 : ℚ) : ℝ) ≤ stT254 75 := by
  have hc : ((-978467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1129836823367/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-978467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c76 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((908621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 215413/2000000) (δ := 2569/200000000) (ψ := 563/31250) 254 175
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t76 : ((521100902769/5000000000000 : ℚ) : ℝ) ≤ stT254 76 := by
  have hc : ((908571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((521100902769/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((908571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c77 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-819907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3165057/5000000) (δ := 2573/200000000) (ψ := 563/31250) 254 176
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t77 : ((-467213958471/5000000000000 : ℚ) : ℝ) ≤ stT254 77 := by
  have hc : ((-819957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-467213958471/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-819957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c78 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((183701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 372709/2000000) (δ := 2573/200000000) (ψ := 563/31250) 254 176
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t78 : ((415972527429/5000000000000 : ℚ) : ℝ) ≤ stT254 78 := by
  have hc : ((367377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((415972527429/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((367377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c79 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-166953/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2877577/5000000) (δ := 12831/1000000000) (ψ := 563/31250) 254 177
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t79 : ((-11740680029/156250000000 : ℚ) : ℝ) ≤ stT254 79 := by
  have hc : ((-333931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11740680029/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-333931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c80 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((313557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34881/156250) (δ := 12831/1000000000) (ψ := 563/31250) 254 177
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t80 : ((87634780639/1250000000000 : ℚ) : ℝ) ≤ stT254 80 := by
  have hc : ((78383/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87634780639/1250000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((78383/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c81 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-308183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5587291/10000000) (δ := 12879/1000000000) (ψ := 563/31250) 254 178
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t81 : ((-2675418807/39062500000 : ℚ) : ℝ) ≤ stT254 81 := by
  have hc : ((-19263/31250 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2675418807/39062500000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-19263/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c82 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((635849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1102111/5000000) (δ := 3181/250000000) (ψ := 563/31250) 254 178
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t82 : ((140424474537/2000000000000 : ℚ) : ℝ) ≤ stT254 82 := by
  have hc : ((635799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140424474537/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((635799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c83 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-341501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1451663/2500000) (δ := 12787/1000000000) (ψ := 563/31250) 254 179
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t83 : ((-187436811609/2500000000000 : ℚ) : ℝ) ≤ stT254 83 := by
  have hc : ((-170763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187436811609/2500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-170763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c84 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((18807/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1798203/10000000) (δ := 3177/125000000) (ψ := 563/31250) 254 179
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t84 : ((82074987847/1000000000000 : ℚ) : ℝ) ≤ stT254 84 := by
  have hc : ((75223/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82074987847/1000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((75223/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c85 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-834463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1598721/2500000) (δ := 6447/500000000) (ψ := 563/31250) 254 180
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t85 : ((-905157028989/10000000000000 : ℚ) : ℝ) ≤ stT254 85 := by
  have hc : ((-834513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-905157028989/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-834513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c86 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((915989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258019/2500000) (δ := 6447/500000000) (ψ := 563/31250) 254 180
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t86 : ((987681754053/10000000000000 : ℚ) : ℝ) ≤ stT254 86 := by
  have hc : ((915939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((987681754053/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((915939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c87 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-489253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1833679/2500000) (δ := 12801/1000000000) (ψ := 563/31250) 254 181
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t87 : ((-262280652207/2500000000000 : ℚ) : ℝ) ≤ stT254 87 := by
  have hc : ((-244639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262280652207/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-244639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c88 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((6247/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19373/2500000) (δ := 6401/500000000) (ψ := 563/31250) 254 181
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t88 : ((106543801841/1000000000000 : ℚ) : ℝ) ≤ stT254 88 := by
  have hc : ((99947/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106543801841/1000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((99947/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c89 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-95459/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7097691/10000000) (δ := 12801/1000000000) (ψ := 563/31250) 254 181
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t89 : ((-6324478067/62500000000 : ℚ) : ℝ) ≤ stT254 89 := by
  have hc : ((-11933/12500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6324478067/62500000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-11933/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c90 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((821881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1515227/10000000) (δ := 3177/250000000) (ψ := 563/31250) 254 182
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t90 : ((216571370613/2500000000000 : ℚ) : ℝ) ≤ stT254 90 := by
  have hc : ((821831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216571370613/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((821831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c91 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-588963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1375357/2500000) (δ := 6377/250000000) (ψ := 563/31250) 254 182
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t91 : ((-123490698541/2000000000000 : ℚ) : ℝ) ≤ stT254 91 := by
  have hc : ((-589013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123490698541/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-589013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c92 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((261099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3266589/10000000) (δ := 3197/250000000) (ψ := 563/31250) 254 183
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t92 : ((68040594507/2500000000000 : ℚ) : ℝ) ≤ stT254 92 := by
  have hc : ((261049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68040594507/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((261049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c93 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((26217/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3598333/10000000) (δ := 2563/200000000) (ψ := 563/31250) 254 183
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t93 : ((27175374857/2000000000000 : ℚ) : ℝ) ≤ stT254 93 := by
  have hc : ((26207/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27175374857/2000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((26207/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c94 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-21127/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1063623/2000000) (δ := 12723/1000000000) (ψ := 563/31250) 254 184
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t94 : ((-10896457719/200000000000 : ℚ) : ℝ) ≤ stT254 94 := by
  have hc : ((-21129/40000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10896457719/200000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-21129/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c95 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((211733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 700759/5000000) (δ := 161/12500000) (ψ := 563/31250) 254 184
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t95 : ((217220575149/2500000000000 : ℚ) : ℝ) ≤ stT254 95 := by
  have hc : ((423441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217220575149/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((423441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c96 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-996903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7657169/10000000) (δ := 1283/100000000) (ψ := 563/31250) 254 185
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t96 : ((-1017511167813/10000000000000 : ℚ) : ℝ) ≤ stT254 96 := by
  have hc : ((-996953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1017511167813/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-996953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c97 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((908667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1076791/10000000) (δ := 1283/100000000) (ψ := 563/31250) 254 185
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t97 : ((461280318241/5000000000000 : ℚ) : ℝ) ≤ stT254 97 := by
  have hc : ((908617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461280318241/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((908617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c98 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-567641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2718043/5000000) (δ := 12773/1000000000) (ψ := 563/31250) 254 185
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t98 : ((-573454766723/10000000000000 : ℚ) : ℝ) ≤ stT254 98 := by
  have hc : ((-567691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573454766723/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-567691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c99 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((5093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3825103/10000000) (δ := 12737/1000000000) (ψ := 563/31250) 254 186
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t99 : ((20449487839/5000000000000 : ℚ) : ℝ) ≤ stT254 99 := by
  have hc : ((20347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20449487839/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((20347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c100 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((260517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2556837/10000000) (δ := 6433/500000000) (ψ := 563/31250) 254 186
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t100 : ((65122934877/1250000000000 : ℚ) : ℝ) ≤ stT254 100 := by
  have hc : ((65123/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65122934877/1250000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((65123/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c101 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-9177/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3416311/5000000) (δ := 12759/1000000000) (ψ := 563/31250) 254 187
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t101 : ((-1826392249/20000000000 : ℚ) : ℝ) ≤ stT254 101 := by
  have hc : ((-3671/4000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1826392249/20000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-3671/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c102 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((486769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -576411/10000000) (δ := 3211/250000000) (ψ := 563/31250) 254 187
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t102 : ((60243513921/625000000000 : ℚ) : ℝ) ≤ stT254 102 := by
  have hc : ((60843/62500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60243513921/625000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((60843/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c103 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-125243/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 702339/1250000) (δ := 12759/1000000000) (ψ := 563/31250) 254 187
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t103 : ((-12341553849/200000000000 : ℚ) : ℝ) ≤ stT254 103 := by
  have hc : ((-125253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12341553849/200000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-125253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c104 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-10781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -790789/2000000) (δ := 3213/250000000) (ψ := 563/31250) 254 188
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t104 : ((-10620672811/10000000000000 : ℚ) : ℝ) ≤ stT254 104 := by
  have hc : ((-10831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10620672811/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-10831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c105 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((330339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33167/156250) (δ := 12751/1000000000) (ψ := 563/31250) 254 188
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t105 : ((1611767163/25000000000 : ℚ) : ℝ) ≤ stT254 105 := by
  have hc : ((165157/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1611767163/25000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((165157/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c106 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-496693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7566301/10000000) (δ := 2549/200000000) (ψ := 563/31250) 254 189
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t106 : ((-120613809837/1250000000000 : ℚ) : ℝ) ≤ stT254 106 := by
  have hc : ((-248359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120613809837/1250000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-248359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c107 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((100149/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -801889/5000000) (δ := 2549/200000000) (ψ := 563/31250) 254 189
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t107 : ((24202900391/312500000000 : ℚ) : ℝ) ≤ stT254 107 := by
  have hc : ((400571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24202900391/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((400571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c108 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-29987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2151623/5000000) (δ := 2549/200000000) (ψ := 563/31250) 254 189
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t108 : ((-28864643247/2000000000000 : ℚ) : ℝ) ≤ stT254 108 := by
  have hc : ((-29997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28864643247/2000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-29997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c109 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-121049/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347011/625000) (δ := 6383/500000000) (ψ := 563/31250) 254 190
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t109 : ((-115953578793/2000000000000 : ℚ) : ℝ) ≤ stT254 109 := by
  have hc : ((-121059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115953578793/2000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-121059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c110 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((7961/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246961/10000000) (δ := 12837/1000000000) (ψ := 563/31250) 254 190
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t110 : ((18975323993/200000000000 : ℚ) : ℝ) ≤ stT254 110 := by
  have hc : ((39803/40000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18975323993/200000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((39803/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c111 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-29427/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 374603/625000) (δ := 6383/500000000) (ψ := 563/31250) 254 190
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t111 : ((-13966385391/200000000000 : ℚ) : ℝ) ≤ stT254 111 := by
  have hc : ((-29429/40000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13966385391/200000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-29429/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c112 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-36897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2009627/5000000) (δ := 12873/1000000000) (ψ := 563/31250) 254 191
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t112 : ((-2181978979/625000000000 : ℚ) : ℝ) ≤ stT254 112 := by
  have hc : ((-36947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2181978979/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-36947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c113 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((796021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1625261/10000000) (δ := 12873/1000000000) (ψ := 563/31250) 254 191
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t113 : ((9359822989/125000000000 : ℚ) : ℝ) ≤ stT254 113 := by
  have hc : ((795971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9359822989/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((795971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c114 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-968017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 902499/1250000) (δ := 12873/1000000000) (ψ := 563/31250) 254 191
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t114 : ((-453338999631/5000000000000 : ℚ) : ℝ) ≤ stT254 114 := by
  have hc : ((-968067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453338999631/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-968067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c115 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((76771/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367759/1250000) (δ := 639/50000000) (ψ := 563/31250) 254 192
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t115 : ((8947492443/250000000000 : ℚ) : ℝ) ≤ stT254 115 := by
  have hc : ((76761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8947492443/250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((76761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c116 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((260701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1277879/5000000) (δ := 639/50000000) (ψ := 563/31250) 254 192
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t116 : ((15126963111/312500000000 : ℚ) : ℝ) ≤ stT254 116 := by
  have hc : ((65169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15126963111/312500000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((65169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c117 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-49907/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1925373/2500000) (δ := 12887/1000000000) (ψ := 563/31250) 254 193
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t117 : ((-92282765319/1000000000000 : ℚ) : ℝ) ≤ stT254 117 := by
  have hc : ((-99819/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92282765319/1000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-99819/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c118 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((606711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1148599/5000000) (δ := 3179/250000000) (ψ := 563/31250) 254 193
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t118 : ((279238171707/5000000000000 : ℚ) : ℝ) ≤ stT254 118 := by
  have hc : ((606661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279238171707/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((606661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c119 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((67869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9567/31250) (δ := 3179/250000000) (ψ := 563/31250) 254 193
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t119 : ((31103104791/1000000000000 : ℚ) : ℝ) ≤ stT254 119 := by
  have hc : ((67859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31103104791/1000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((67859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c120 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-30573/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7332653/10000000) (δ := 12809/1000000000) (ψ := 563/31250) 254 194
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t120 : ((-446570103103/5000000000000 : ℚ) : ℝ) ≤ stT254 120 := by
  have hc : ((-489193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-446570103103/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-489193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c121 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((135687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -412583/2000000) (δ := 12809/1000000000) (ψ := 563/31250) 254 194
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t121 : ((12334260393/200000000000 : ℚ) : ℝ) ≤ stT254 121 := by
  have hc : ((135677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12334260393/200000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((135677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c122 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((300689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3163453/10000000) (δ := 6397/500000000) (ψ := 563/31250) 254 194
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t122 : ((272185623123/10000000000000 : ℚ) : ℝ) ≤ stT254 122 := by
  have hc : ((300639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272185623123/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((300639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c123 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-490303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1472163/2000000) (δ := 6351/500000000) (ψ := 563/31250) 254 195
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t123 : ((-5526425597/62500000000 : ℚ) : ℝ) ≤ stT254 123 := by
  have hc : ((-61291/62500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5526425597/62500000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-61291/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c124 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((315623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2219093/10000000) (δ := 6351/500000000) (ψ := 563/31250) 254 195
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t124 : ((70853802387/1250000000000 : ℚ) : ℝ) ≤ stT254 124 := by
  have hc : ((157799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70853802387/1250000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((157799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c125 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((203083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1440677/5000000) (δ := 6351/500000000) (ψ := 563/31250) 254 195
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t125 : ((90810278883/2500000000000 : ℚ) : ℝ) ≤ stT254 125 := by
  have hc : ((101529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90810278883/2500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((101529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c126 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-31231/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3883401/5000000) (δ := 12809/1000000000) (ψ := 563/31250) 254 196
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t126 : ((-445186946991/5000000000000 : ℚ) : ℝ) ≤ stT254 126 := by
  have hc : ((-499721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-445186946991/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-499721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c127 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((227321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343383/1250000) (δ := 6397/500000000) (ψ := 563/31250) 254 196
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t127 : ((1575722417/39062500000 : ℚ) : ℝ) ≤ stT254 127 := by
  have hc : ((7103/15625 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1575722417/39062500000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((7103/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c128 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((626807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279171/1250000) (δ := 6397/500000000) (ψ := 563/31250) 254 196
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t128 : ((553979857431/10000000000000 : ℚ) : ℝ) ≤ stT254 128 := by
  have hc : ((626757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((553979857431/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((626757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c129 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-120419/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1435013/2000000) (δ := 6397/500000000) (ψ := 563/31250) 254 196
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t129 : ((-424114127151/5000000000000 : ℚ) : ℝ) ≤ stT254 129 := by
  have hc : ((-481701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424114127151/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-481701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c130 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((14843/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -907357/2500000) (δ := 3179/250000000) (ψ := 563/31250) 254 197
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t130 : ((26025380563/2500000000000 : ℚ) : ℝ) ≤ stT254 130 := by
  have hc : ((59347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26025380563/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((59347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c131 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((220039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1236513/10000000) (δ := 12887/1000000000) (ψ := 563/31250) 254 197
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t131 : ((48059508289/625000000000 : ℚ) : ℝ) ≤ stT254 131 := by
  have hc : ((440053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48059508289/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((440053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c132 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-377409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3032717/5000000) (δ := 12887/1000000000) (ψ := 563/31250) 254 197
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t132 : ((-164257200913/2500000000000 : ℚ) : ℝ) ≤ stT254 132 := by
  have hc : ((-188717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164257200913/2500000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-188717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c133 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-180447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4850057/10000000) (δ := 639/50000000) (ψ := 563/31250) 254 198
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t133 : ((-1956113449/62500000000 : ℚ) : ℝ) ≤ stT254 133 := by
  have hc : ((-22559/62500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1956113449/62500000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-22559/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c134 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((999301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46747/5000000) (δ := 25423/1000000000) (ψ := 563/31250) 254 198
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t134 : ((215805240717/2500000000000 : ℚ) : ℝ) ≤ stT254 134 := by
  have hc : ((999251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215805240717/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((999251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c135 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-69157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4627699/10000000) (δ := 639/50000000) (ψ := 563/31250) 254 198
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t135 : ((-119063258757/5000000000000 : ℚ) : ℝ) ≤ stT254 135 := by
  have hc : ((-138339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119063258757/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-138339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c136 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-417123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6393901/10000000) (δ := 12873/1000000000) (ψ := 563/31250) 254 199
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t136 : ((-89425372491/1250000000000 : ℚ) : ℝ) ≤ stT254 136 := by
  have hc : ((-104287/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89425372491/1250000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-104287/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c137 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((23967/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1741827/10000000) (δ := 1273/100000000) (ψ := 563/31250) 254 199
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t137 : ((327600628579/5000000000000 : ℚ) : ℝ) ≤ stT254 137 := by
  have hc : ((383447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327600628579/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((383447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c138 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((407999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2876337/10000000) (δ := 12873/1000000000) (ψ := 563/31250) 254 199
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t138 : ((43408629243/1250000000000 : ℚ) : ℝ) ≤ stT254 138 := by
  have hc : ((407949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43408629243/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((407949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c139 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-197537/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1865307/2500000) (δ := 1273/100000000) (ψ := 563/31250) 254 199
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t139 : ((-167557192383/2000000000000 : ℚ) : ℝ) ≤ stT254 139 := by
  have hc : ((-197547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167557192383/2000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-197547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c140 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((2899/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1847369/5000000) (δ := 6383/500000000) (ψ := 563/31250) 254 200
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t140 : ((19590247143/2500000000000 : ℚ) : ℝ) ≤ stT254 140 := by
  have hc : ((46359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19590247143/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((46359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c141 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((946067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 824811/10000000) (δ := 6383/500000000) (ψ := 563/31250) 254 200
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t141 : ((796689162567/10000000000000 : ℚ) : ℝ) ≤ stT254 141 := by
  have hc : ((946017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((796689162567/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((946017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c142 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-526261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5312483/10000000) (δ := 6383/500000000) (ψ := 563/31250) 254 200
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t142 : ((-220835358801/5000000000000 : ℚ) : ℝ) ≤ stT254 142 := by
  have hc : ((-526311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220835358801/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-526311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c143 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-720779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742413/1250000) (δ := 2549/200000000) (ψ := 563/31250) 254 201
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t143 : ((-602788205447/10000000000000 : ℚ) : ℝ) ≤ stT254 143 := by
  have hc : ((-720829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-602788205447/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-720829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c144 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((164421/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1514243/10000000) (δ := 2549/200000000) (ψ := 563/31250) 254 201
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t144 : ((137009111863/2000000000000 : ℚ) : ℝ) ≤ stT254 144 := by
  have hc : ((164411/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137009111863/2000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((164411/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c145 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((406561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1440137/5000000) (δ := 6429/500000000) (ψ := 563/31250) 254 201
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t145 : ((168794342997/5000000000000 : ℚ) : ℝ) ≤ stT254 145 := by
  have hc : ((406511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168794342997/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((406511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c146 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-242609/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3622283/5000000) (δ := 2549/200000000) (ψ := 563/31250) 254 201
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t146 : ((-200795009129/2500000000000 : ℚ) : ℝ) ≤ stT254 146 := by
  have hc : ((-485243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200795009129/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-485243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c147 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-10087/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4128951/10000000) (δ := 12751/1000000000) (ψ := 563/31250) 254 202
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t147 : ((-33299125551/5000000000000 : ℚ) : ℝ) ≤ stT254 147 := by
  have hc : ((-40373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33299125551/5000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-40373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c148 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((498759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176159/10000000) (δ := 3213/250000000) (ψ := 563/31250) 254 202
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t148 : ((102489088899/1250000000000 : ℚ) : ℝ) ≤ stT254 148 := by
  have hc : ((249367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102489088899/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((249367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c149 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-104293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 556539/1250000) (δ := 12751/1000000000) (ψ := 563/31250) 254 202
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t149 : ((-1335322559/78125000000 : ℚ) : ℝ) ≤ stT254 149 := by
  have hc : ((-52159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1335322559/78125000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-52159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c150 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-235829/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35041/50000) (δ := 3211/250000000) (ψ := 563/31250) 254 203
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t150 : ((-385127754451/5000000000000 : ℚ) : ℝ) ≤ stT254 150 := by
  have hc : ((-471683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385127754451/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-471683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c151 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((219841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2788879/10000000) (δ := 3211/250000000) (ψ := 563/31250) 254 203
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t151 : ((5590113219/156250000000 : ℚ) : ℝ) ≤ stT254 151 := by
  have hc : ((27477/62500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5590113219/156250000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((27477/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c152 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((846709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701283/5000000) (δ := 12759/1000000000) (ψ := 563/31250) 254 203
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t152 : ((686731041513/10000000000000 : ℚ) : ℝ) ≤ stT254 152 := by
  have hc : ((846659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((686731041513/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((846659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c153 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-609801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113303/2000000) (δ := 12759/1000000000) (ψ := 563/31250) 254 203
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t153 : ((-493035870503/10000000000000 : ℚ) : ℝ) ≤ stT254 153 := by
  have hc : ((-609851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-493035870503/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-609851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c154 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-738639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3002307/5000000) (δ := 12737/1000000000) (ψ := 563/31250) 254 204
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t154 : ((-595252586047/10000000000000 : ℚ) : ℝ) ≤ stT254 154 := by
  have hc : ((-738689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-595252586047/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-738689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c155 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((726329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118411/625000) (δ := 6433/500000000) (ψ := 563/31250) 254 204
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t155 : ((583361092101/10000000000000 : ℚ) : ℝ) ≤ stT254 155 := by
  have hc : ((726279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583361092101/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((726279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c156 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((320261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 437809/2000000) (δ := 12737/1000000000) (ψ := 563/31250) 254 204
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t156 : ((100153809/1953125000 : ℚ) : ℝ) ≤ stT254 156 := by
  have hc : ((80059/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100153809/1953125000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((80059/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c157 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-800321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 780821/1250000) (δ := 12737/1000000000) (ψ := 563/31250) 254 204
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t157 : ((-638765690277/10000000000000 : ℚ) : ℝ) ≤ stT254 157 := by
  have hc : ((-800371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638765690277/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-800371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c158 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-565521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5429653/10000000) (δ := 12773/1000000000) (ψ := 563/31250) 254 205
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t158 : ((-224972266809/5000000000000 : ℚ) : ℝ) ≤ stT254 158 := by
  have hc : ((-565571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224972266809/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-565571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c159 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((168453/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1423311/10000000) (δ := 12773/1000000000) (ψ := 563/31250) 254 205
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t159 : ((133583889593/2000000000000 : ℚ) : ℝ) ≤ stT254 159 := by
  have hc : ((168443/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133583889593/2000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((168443/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c160 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((130169/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 511577/2000000) (δ := 12773/1000000000) (ψ := 563/31250) 254 205
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t160 : ((205795388097/5000000000000 : ℚ) : ℝ) ≤ stT254 160 := by
  have hc : ((260313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205795388097/5000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((260313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c161 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-429907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628563/2500000) (δ := 1283/100000000) (ψ := 563/31250) 254 205
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t161 : ((-84708534613/1250000000000 : ℚ) : ℝ) ≤ stT254 161 := by
  have hc : ((-107483/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84708534613/1250000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-107483/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c162 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-31807/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5261791/10000000) (δ := 12723/1000000000) (ψ := 563/31250) 254 206
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t162 : ((-7997574387/200000000000 : ℚ) : ℝ) ≤ stT254 162 := by
  have hc : ((-254481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7997574387/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-254481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c163 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((107109/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84629/625000) (δ := 161/12500000) (ψ := 563/31250) 254 206
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t163 : ((16777859993/250000000000 : ℚ) : ℝ) ≤ stT254 163 := by
  have hc : ((428411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16777859993/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((428411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c164 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((26513/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2529723/10000000) (δ := 161/12500000) (ψ := 563/31250) 254 206
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t164 : ((10350600557/250000000000 : ℚ) : ℝ) ≤ stT254 164 := by
  have hc : ((53021/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10350600557/250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((53021/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c165 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-10417/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49921/78125) (δ := 161/12500000) (ψ := 563/31250) 254 206
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t165 : ((-64880885159/1000000000000 : ℚ) : ℝ) ≤ stT254 165 := by
  have hc : ((-83341/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64880885159/1000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-83341/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c166 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-58241/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1096243/2000000) (δ := 3197/250000000) (ψ := 563/31250) 254 207
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t166 : ((-22603845573/500000000000 : ℚ) : ℝ) ≤ stT254 166 := by
  have hc : ((-29123/50000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22603845573/500000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-29123/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c167 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((19643/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -833671/5000000) (δ := 2563/200000000) (ψ := 563/31250) 254 207
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t167 : ((60796951641/1000000000000 : ℚ) : ℝ) ≤ stT254 167 := by
  have hc : ((78567/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60796951641/1000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((78567/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c168 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((330191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265459/1250000) (δ := 3197/250000000) (ψ := 563/31250) 254 207
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t168 : ((31841043957/625000000000 : ℚ) : ℝ) ≤ stT254 168 := by
  have hc : ((165083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31841043957/625000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((165083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c169 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-707611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589227/1000000) (δ := 3197/250000000) (ψ := 563/31250) 254 207
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t169 : ((-544354778691/10000000000000 : ℚ) : ℝ) ≤ stT254 169 := by
  have hc : ((-707661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-544354778691/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-707661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c170 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-377927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -758673/1250000) (δ := 3177/250000000) (ψ := 563/31250) 254 208
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t170 : ((-1811724723/31250000000 : ℚ) : ℝ) ≤ stT254 170 := by
  have hc : ((-11811/15625 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1811724723/31250000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-11811/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c171 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((591387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -469009/2000000) (δ := 2579/200000000) (ψ := 563/31250) 254 208
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t171 : ((452206639303/10000000000000 : ℚ) : ℝ) ≤ stT254 171 := by
  have hc : ((591337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452206639303/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((591337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c172 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((856147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169697/1250000) (δ := 3177/250000000) (ψ := 563/31250) 254 208
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t172 : ((163191778431/2500000000000 : ℚ) : ℝ) ≤ stT254 172 := by
  have hc : ((856097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163191778431/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((856097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c173 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-86037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1007747/2000000) (δ := 2579/200000000) (ψ := 563/31250) 254 208
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t173 : ((-32710164721/1000000000000 : ℚ) : ℝ) ≤ stT254 173 := by
  have hc : ((-86047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32710164721/1000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-86047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c174 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-943459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7009279/10000000) (δ := 6401/500000000) (ψ := 563/31250) 254 209
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t174 : ((-715273229391/10000000000000 : ℚ) : ℝ) ≤ stT254 174 := by
  have hc : ((-943509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-715273229391/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-943509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c175 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((220847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -674057/2000000) (δ := 12801/1000000000) (ψ := 563/31250) 254 209
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t175 : ((20863329327/1250000000000 : ℚ) : ℝ) ≤ stT254 175 := by
  have hc : ((220797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20863329327/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((220797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c176 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((497543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49589/2000000) (δ := 12801/1000000000) (ψ := 563/31250) 254 209
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t176 : ((93754530751/1250000000000 : ℚ) : ℝ) ≤ stT254 176 := by
  have hc : ((248759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93754530751/1250000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((248759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c177 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((32499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120179/312500) (δ := 12801/1000000000) (ψ := 563/31250) 254 209
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t177 : ((12195080527/5000000000000 : ℚ) : ℝ) ≤ stT254 177 := by
  have hc : ((32449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12195080527/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((32449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c178 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-98519/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7423191/10000000) (δ := 12801/1000000000) (ψ := 563/31250) 254 209
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t178 : ((-4615430673/62500000000 : ℚ) : ℝ) ≤ stT254 178 := by
  have hc : ((-24631/25000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4615430673/62500000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-24631/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c179 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-314689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295457/625000) (δ := 6447/500000000) (ψ := 563/31250) 254 210
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t179 : ((-58811814801/2500000000000 : ℚ) : ℝ) ≤ stT254 179 := by
  have hc : ((-314739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58811814801/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-314739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c180 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((177777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1189727/10000000) (δ := 6447/500000000) (ψ := 563/31250) 254 210
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t180 : ((26499904457/400000000000 : ℚ) : ℝ) ≤ stT254 180 := by
  have hc : ((177767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26499904457/400000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((177767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c181 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((23871/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23283/100000) (δ := 6447/500000000) (ψ := 563/31250) 254 210
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t181 : ((8870842243/200000000000 : ℚ) : ℝ) ≤ stT254 181 := by
  have hc : ((23869/40000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8870842243/200000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((23869/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c182 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-344447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 364181/625000) (δ := 6447/500000000) (ψ := 563/31250) 254 210
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t182 : ((-25533987/500000000 : ℚ) : ℝ) ≤ stT254 182 := by
  have hc : ((-43059/62500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25533987/500000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-43059/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c183 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-835937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -400099/625000) (δ := 801/62500000) (ψ := 563/31250) 254 211
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t183 : ((-308989991057/5000000000000 : ℚ) : ℝ) ≤ stT254 183 := by
  have hc : ((-835987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308989991057/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-835987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c184 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((192109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91909/312500) (δ := 801/62500000) (ψ := 563/31250) 254 211
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t184 : ((35401513389/1250000000000 : ℚ) : ℝ) ≤ stT254 184 := by
  have hc : ((48021/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35401513389/1250000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((48021/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c185 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((980013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20027/400000) (δ := 12787/1000000000) (ψ := 563/31250) 254 211
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t185 : ((360241258541/5000000000000 : ℚ) : ℝ) ≤ stT254 185 := by
  have hc : ((979963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360241258541/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((979963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c186 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((1263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3923833/10000000) (δ := 12787/1000000000) (ψ := 563/31250) 254 211
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t186 : ((177882811/2000000000000 : ℚ) : ℝ) ≤ stT254 186 := by
  have hc : ((1213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177882811/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((1213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c187 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-122251/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7328703/10000000) (δ := 12787/1000000000) (ψ := 563/31250) 254 211
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t187 : ((-357613703917/5000000000000 : ℚ) : ℝ) ≤ stT254 187 := by
  have hc : ((-489029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-357613703917/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-489029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c188 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-413459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -998523/2000000) (δ := 12879/1000000000) (ψ := 563/31250) 254 212
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t188 : ((-12063298057/400000000000 : ℚ) : ℝ) ≤ stT254 188 := by
  have hc : ((-413509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12063298057/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-413509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c189 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((199089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405969/2500000) (δ := 3181/250000000) (ψ := 563/31250) 254 212
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t189 : ((9050415843/156250000000 : ℚ) : ℝ) ≤ stT254 189 := by
  have hc : ((398153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9050415843/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((398153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c190 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((192683/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1727019/10000000) (δ := 3181/250000000) (ψ := 563/31250) 254 212
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t190 : ((69888911829/1250000000000 : ℚ) : ℝ) ≤ stT254 190 := by
  have hc : ((385341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69888911829/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((385341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c191 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-109497/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1265097/2500000) (δ := 3181/250000000) (ψ := 563/31250) 254 212
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t191 : ((-6339066917/200000000000 : ℚ) : ℝ) ≤ stT254 191 := by
  have hc : ((-219019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6339066917/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-219019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c192 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-489127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7331669/10000000) (δ := 3193/250000000) (ψ := 563/31250) 254 213
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t192 : ((-689482673/9765625000 : ℚ) : ℝ) ≤ stT254 192 := by
  have hc : ((-15286/15625 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-689482673/9765625000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-15286/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c193 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-42379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4032971/10000000) (δ := 3193/250000000) (ψ := 563/31250) 254 213
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t193 : ((-3817634133/1250000000000 : ℚ) : ℝ) ≤ stT254 193 := by
  have hc : ((-42429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3817634133/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-42429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c194 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((59699/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -751291/10000000) (δ := 3193/250000000) (ψ := 563/31250) 254 213
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t194 : ((171436524093/2500000000000 : ℚ) : ℝ) ≤ stT254 194 := by
  have hc : ((477567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171436524093/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((477567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c195 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((535751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1256749/5000000) (δ := 3193/250000000) (ψ := 563/31250) 254 213
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t195 : ((191811492957/5000000000000 : ℚ) : ℝ) ≤ stT254 195 := by
  have hc : ((535701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191811492957/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((535701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c196 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-26789/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5761587/10000000) (δ := 12831/1000000000) (ψ := 563/31250) 254 213
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t196 : ((-9568218113/200000000000 : ℚ) : ℝ) ≤ stT254 196 := by
  have hc : ((-26791/40000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9568218113/200000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-26791/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c197 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-179593/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3357399/5000000) (δ := 6369/500000000) (ψ := 563/31250) 254 214
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t197 : ((-127961929013/2000000000000 : ℚ) : ℝ) ≤ stT254 197 := by
  have hc : ((-179603/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127961929013/2000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-179603/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c198 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((42531/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3499603/10000000) (δ := 2573/200000000) (ψ := 563/31250) 254 214
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t198 : ((60433159753/5000000000000 : ℚ) : ℝ) ≤ stT254 198 := by
  have hc : ((85037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60433159753/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((85037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c199 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((49639/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1503/50000) (δ := 2573/200000000) (ψ := 563/31250) 254 214
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t199 : ((70372743513/1000000000000 : ℚ) : ℝ) ≤ stT254 199 := by
  have hc : ((99273/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70372743513/1000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((99273/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c200 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((405807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1441169/5000000) (δ := 6369/500000000) (ψ := 563/31250) 254 214
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t200 : ((143456604621/5000000000000 : ℚ) : ℝ) ≤ stT254 200 := by
  have hc : ((405757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143456604621/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((405757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c201 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-750613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756183/1250000) (δ := 6369/500000000) (ψ := 563/31250) 254 214
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t201 : ((-264738572199/5000000000000 : ℚ) : ℝ) ≤ stT254 201 := by
  have hc : ((-750663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264738572199/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-750663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c202 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-858367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1301437/2000000) (δ := 6379/500000000) (ψ := 563/31250) 254 215
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t202 : ((-301990242183/5000000000000 : ℚ) : ℝ) ≤ stT254 202 := by
  have hc : ((-858417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301990242183/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-858417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c203 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((110213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -842841/2500000) (δ := 2569/200000000) (ψ := 563/31250) 254 215
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t203 : ((9667096257/625000000000 : ℚ) : ℝ) ≤ stT254 203 := by
  have hc : ((27547/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9667096257/625000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((27547/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c204 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((198993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125487/5000000) (δ := 2569/200000000) (ψ := 563/31250) 254 215
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t204 : ((6965797881/100000000000 : ℚ) : ℝ) ≤ stT254 204 := by
  have hc : ((198983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6965797881/100000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((198983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c205 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((104019/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89193/312500) (δ := 2569/200000000) (ψ := 563/31250) 254 215
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t205 : ((14528251959/500000000000 : ℚ) : ℝ) ≤ stT254 205 := by
  have hc : ((208013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14528251959/500000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((208013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c206 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-722139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5944213/10000000) (δ := 2569/200000000) (ψ := 563/31250) 254 215
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t206 : ((-251586815363/5000000000000 : ℚ) : ℝ) ≤ stT254 206 := by
  have hc : ((-722189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251586815363/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-722189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c207 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-446661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66887/100000) (δ := 12851/1000000000) (ψ := 563/31250) 254 216
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t207 : ((-155234328807/2500000000000 : ℚ) : ℝ) ≤ stT254 207 := by
  have hc : ((-223343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155234328807/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-223343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c208 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((23827/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -907111/2500000) (δ := 797/62500000) (ψ := 563/31250) 254 216
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t208 : ((132112899/16000000000 : ℚ) : ℝ) ≤ stT254 208 := by
  have hc : ((23817/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132112899/16000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((23817/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c209 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((194589/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -582857/10000000) (δ := 797/62500000) (ψ := 563/31250) 254 216
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t209 : ((67296509203/1000000000000 : ℚ) : ℝ) ≤ stT254 209 := by
  have hc : ((194579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67296509203/1000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((194579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c210 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((69703/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 612047/2500000) (δ := 12851/1000000000) (ψ := 563/31250) 254 216
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t210 : ((38476230231/1000000000000 : ℚ) : ℝ) ≤ stT254 210 := by
  have hc : ((278787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38476230231/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((278787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c211 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-288533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5464819/10000000) (δ := 12851/1000000000) (ψ := 563/31250) 254 216
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t211 : ((-99325847691/2500000000000 : ℚ) : ℝ) ≤ stT254 211 := by
  have hc : ((-144279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99325847691/2500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-144279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c212 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-970071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9051/12500) (δ := 12859/1000000000) (ψ := 563/31250) 254 217
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t212 : ((-666282013163/10000000000000 : ℚ) : ℝ) ≤ stT254 212 := by
  have hc : ((-970121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-666282013163/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-970121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c213 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-64929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2126277/5000000) (δ := 1593/125000000) (ψ := 563/31250) 254 217
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t213 : ((-22252883153/2500000000000 : ℚ) : ℝ) ≤ stT254 213 := by
  have hc : ((-32477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22252883153/2500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-32477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c214 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((109013/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1278277/10000000) (δ := 12859/1000000000) (ψ := 563/31250) 254 217
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t214 : ((59612303359/1000000000000 : ℚ) : ℝ) ≤ stT254 214 := by
  have hc : ((436027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59612303359/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((436027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c215 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((782057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1682093/10000000) (δ := 12859/1000000000) (ψ := 563/31250) 254 217
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t215 : ((266662040979/5000000000000 : ℚ) : ℝ) ≤ stT254 215 := by
  have hc : ((782007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266662040979/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((782007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c216 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-277031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4628747/10000000) (δ := 12859/1000000000) (ψ := 563/31250) 254 217
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t216 : ((-94264895767/5000000000000 : ℚ) : ℝ) ≤ stT254 216 := by
  have hc : ((-277081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94264895767/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-277081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c217 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-124147/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1890437/2500000) (δ := 1593/125000000) (ψ := 563/31250) 254 217
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t217 : ((-67424650397/1000000000000 : ℚ) : ℝ) ≤ stT254 217 := by
  have hc : ((-496613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67424650397/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-496613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c218 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-496771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1306669/2500000) (δ := 3209/250000000) (ψ := 563/31250) 254 218
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t218 : ((-168244953903/5000000000000 : ℚ) : ℝ) ≤ stT254 218 := by
  have hc : ((-496821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168244953903/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-496821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c219 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((119857/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2320471/10000000) (δ := 12767/1000000000) (ψ := 563/31250) 254 218
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t219 : ((80985052239/2000000000000 : ℚ) : ℝ) ≤ stT254 219 := by
  have hc : ((119847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80985052239/2000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((119847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c220 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((973897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 286231/5000000) (δ := 12767/1000000000) (ψ := 563/31250) 254 218
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t220 : ((656566673553/10000000000000 : ℚ) : ℝ) ≤ stT254 220 := by
  have hc : ((973847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((656566673553/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((973847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c221 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((47183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1726157/5000000) (δ := 12767/1000000000) (ψ := 563/31250) 254 218
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t221 : ((1983142161/156250000000 : ℚ) : ℝ) ≤ stT254 221 := by
  have hc : ((94341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1983142161/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((94341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c222 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-408687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1263817/2000000) (δ := 12767/1000000000) (ψ := 563/31250) 254 218
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t222 : ((-34288739973/625000000000 : ℚ) : ℝ) ≤ stT254 222 := by
  have hc : ((-51089/62500 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34288739973/625000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-51089/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c223 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-108001/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3267467/5000000) (δ := 6437/500000000) (ψ := 563/31250) 254 219
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t223 : ((-5786164397/100000000000 : ℚ) : ℝ) ≤ stT254 223 := by
  have hc : ((-432029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5786164397/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-432029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c224 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((93159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1846877/5000000) (δ := 12729/1000000000) (ψ := 563/31250) 254 219
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t224 : ((62211057677/10000000000000 : ℚ) : ℝ) ≤ stT254 224 := by
  have hc : ((93109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62211057677/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((93109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c225 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((235177/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86521/1000000) (δ := 12729/1000000000) (ψ := 563/31250) 254 219
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t225 : ((156776176557/2500000000000 : ℚ) : ℝ) ≤ stT254 225 := by
  have hc : ((470329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156776176557/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((470329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c226 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((177677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1950729/10000000) (δ := 25529/1000000000) (ψ := 563/31250) 254 219
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t226 : ((23636129751/500000000000 : ℚ) : ℝ) ≤ stT254 226 := by
  have hc : ((355329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23636129751/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((355329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c227 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-324911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2377143/5000000) (δ := 12729/1000000000) (ψ := 563/31250) 254 219
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t227 : ((-53921103691/2500000000000 : ℚ) : ℝ) ≤ stT254 227 := by
  have hc : ((-324961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53921103691/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-324961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c228 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-248099/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1886373/2500000) (δ := 12729/1000000000) (ψ := 563/31250) 254 219
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t228 : ((-328632117541/5000000000000 : ℚ) : ℝ) ≤ stT254 228 := by
  have hc : ((-496223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-328632117541/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-496223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c229 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-275093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5383457/10000000) (δ := 12781/1000000000) (ψ := 563/31250) 254 220
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t229 : ((-90901600821/2500000000000 : ℚ) : ℝ) ≤ stT254 229 := by
  have hc : ((-137559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90901600821/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-137559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c230 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((125123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -654143/2500000) (δ := 6411/500000000) (ψ := 563/31250) 254 220
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t230 : ((8249536149/250000000000 : ℚ) : ℝ) ≤ stT254 230 := by
  have hc : ((250221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8249536149/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((250221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c231 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((99847/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17289/1250000) (δ := 6411/500000000) (ψ := 563/31250) 254 220
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t231 : ((32845571871/500000000000 : ℚ) : ℝ) ≤ stT254 231 := by
  have hc : ((49921/50000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32845571871/500000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((49921/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c232 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((406201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1440629/5000000) (δ := 6411/500000000) (ψ := 563/31250) 254 220
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t232 : ((66662782083/2500000000000 : ℚ) : ℝ) ≤ stT254 232 := by
  have hc : ((406151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66662782083/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((406151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c233 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-312131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5612457/10000000) (δ := 12781/1000000000) (ψ := 563/31250) 254 220
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t233 : ((-25562532879/625000000000 : ℚ) : ℝ) ≤ stT254 233 := by
  have hc : ((-78039/125000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25562532879/625000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-78039/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c234 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-490889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -921999/1250000) (δ := 2543/200000000) (ψ := 563/31250) 254 221
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t234 : ((-160460395497/2500000000000 : ℚ) : ℝ) ≤ stT254 234 := by
  have hc : ((-245457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160460395497/2500000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-245457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c235 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-7303/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2334049/5000000) (δ := 2543/200000000) (ψ := 563/31250) 254 221
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t235 : ((-19059096393/1000000000000 : ℚ) : ℝ) ≤ stT254 235 := by
  have hc : ((-29217/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19059096393/1000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-29217/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c236 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((704783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1971697/10000000) (δ := 1611/125000000) (ψ := 563/31250) 254 221
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t236 : ((7167839343/156250000000 : ℚ) : ℝ) ≤ stT254 236 := by
  have hc : ((704733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7167839343/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((704733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c237 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((38383/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 713273/10000000) (δ := 2543/200000000) (ψ := 563/31250) 254 221
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t237 : ((24931107789/400000000000 : ℚ) : ℝ) ≤ stT254 237 := by
  have hc : ((38381/40000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24931107789/400000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((38381/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c238 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((26793/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3386941/10000000) (δ := 1611/125000000) (ψ := 563/31250) 254 221
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t238 : ((69453006841/5000000000000 : ℚ) : ℝ) ≤ stT254 238 := by
  have hc : ((107147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69453006841/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((107147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c239 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-150121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756179/1250000) (δ := 2543/200000000) (ψ := 563/31250) 254 221
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t239 : ((-97111786957/2000000000000 : ℚ) : ℝ) ≤ stT254 239 := by
  have hc : ((-150131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97111786957/2000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-150131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c240 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-943177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -437947/625000) (δ := 2559/200000000) (ψ := 563/31250) 254 222
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t240 : ((-304425571023/5000000000000 : ℚ) : ℝ) ≤ stT254 240 := by
  have hc : ((-943227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304425571023/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-943227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c241 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-87513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2183411/5000000) (δ := 2559/200000000) (ψ := 563/31250) 254 222
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t241 : ((-28194107733/2500000000000 : ℚ) : ℝ) ≤ stT254 241 := by
  have hc : ((-43769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28194107733/2500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-43769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c242 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((192019/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -868707/5000000) (δ := 2559/200000000) (ψ := 563/31250) 254 222
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t242 : ((30856596589/625000000000 : ℚ) : ℝ) ≤ stT254 242 := by
  have hc : ((384013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30856596589/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((384013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c243 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((29329/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176227/2000000) (δ := 1601/125000000) (ψ := 563/31250) 254 222
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t243 : ((602033637/10000000000 : ℚ) : ℝ) ≤ stT254 243 := by
  have hc : ((469239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((602033637/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((469239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c244 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((2179/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3488953/10000000) (δ := 1601/125000000) (ψ := 563/31250) 254 222
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t244 : ((1394560821/125000000000 : ℚ) : ℝ) ≤ stT254 244 := by
  have hc : ((17427/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1394560821/125000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((17427/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c245 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-47513/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 760759/1250000) (δ := 5119/200000000) (ψ := 563/31250) 254 222
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t245 : ((-242855675133/5000000000000 : ℚ) : ℝ) ≤ stT254 245 := by
  have hc : ((-380129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242855675133/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-380129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c246 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-47343/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1407063/2000000) (δ := 129/10000000) (ψ := 563/31250) 254 223
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t246 : ((-60372803707/1000000000000 : ℚ) : ℝ) ≤ stT254 246 := by
  have hc : ((-94691/100000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60372803707/1000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-94691/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c247 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((-105649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4459247/10000000) (δ := 129/10000000) (ψ := 563/31250) 254 223
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t247 : ((-6723878109/500000000000 : ℚ) : ℝ) ≤ stT254 247 := by
  have hc : ((-52837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6723878109/500000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-52837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c248 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((726599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1893593/10000000) (δ := 129/10000000) (ψ := 563/31250) 254 223
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t248 : ((92271723/2000000000 : ℚ) : ℝ) ≤ stT254 248 := by
  have hc : ((726549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92271723/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((726549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c249 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((38607/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 661711/10000000) (δ := 12703/1000000000) (ψ := 563/31250) 254 223
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t249 : ((1223245751/20000000000 : ℚ) : ℝ) ≤ stT254 249 := by
  have hc : ((7721/8000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1223245751/20000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((7721/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_c250 :
    |Real.cos (((254 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((35511/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1603427/5000000) (δ := 129/10000000) (ψ := 563/31250) 254 223
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st254_t250 : ((17964125329/1000000000000 : ℚ) : ℝ) ≤ stT254 250 := by
  have hc : ((142019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((254 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((563/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st254_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17964125329/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((142019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st254_p1 : ((249947/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT254 (i+1) := by
  rw [Finset.sum_range_one]
  exact st254_t1

theorem st254_p2 : ((3404830358111/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT254 (i+1))
      = (∑ i ∈ Finset.range 1, stT254 (i+1)) + stT254 2 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 1
    simpa using h
  have hprev := st254_p1
  have hstep := st254_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p3 : ((12170171519353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT254 (i+1))
      = (∑ i ∈ Finset.range 2, stT254 (i+1)) + stT254 3 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 2
    simpa using h
  have hprev := st254_p2
  have hstep := st254_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p4 : ((17023781519353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT254 (i+1))
      = (∑ i ∈ Finset.range 3, stT254 (i+1)) + stT254 4 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 3
    simpa using h
  have hprev := st254_p3
  have hstep := st254_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p5 : ((10594758567049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT254 (i+1))
      = (∑ i ∈ Finset.range 4, stT254 (i+1)) + stT254 5 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 4
    simpa using h
  have hprev := st254_p4
  have hstep := st254_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p6 : ((218740682573/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT254 (i+1))
      = (∑ i ∈ Finset.range 5, stT254 (i+1)) + stT254 6 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 5
    simpa using h
  have hprev := st254_p5
  have hstep := st254_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p7 : ((1549880189669/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT254 (i+1))
      = (∑ i ∈ Finset.range 6, stT254 (i+1)) + stT254 7 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 6
    simpa using h
  have hprev := st254_p6
  have hstep := st254_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p8 : ((9395799671521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT254 (i+1))
      = (∑ i ∈ Finset.range 7, stT254 (i+1)) + stT254 8 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 7
    simpa using h
  have hprev := st254_p7
  have hstep := st254_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p9 : ((20224255866443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT254 (i+1))
      = (∑ i ∈ Finset.range 8, stT254 (i+1)) + stT254 9 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 8
    simpa using h
  have hprev := st254_p8
  have hstep := st254_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p10 : ((22995681753797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT254 (i+1))
      = (∑ i ∈ Finset.range 9, stT254 (i+1)) + stT254 10 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 9
    simpa using h
  have hprev := st254_p9
  have hstep := st254_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p11 : ((804582239329/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT254 (i+1))
      = (∑ i ∈ Finset.range 10, stT254 (i+1)) + stT254 11 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 10
    simpa using h
  have hprev := st254_p10
  have hstep := st254_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p12 : ((718717785731/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT254 (i+1))
      = (∑ i ∈ Finset.range 11, stT254 (i+1)) + stT254 12 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 11
    simpa using h
  have hprev := st254_p11
  have hstep := st254_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p13 : ((10957656189837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT254 (i+1))
      = (∑ i ∈ Finset.range 12, stT254 (i+1)) + stT254 13 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 12
    simpa using h
  have hprev := st254_p12
  have hstep := st254_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p14 : ((20807169524097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT254 (i+1))
      = (∑ i ∈ Finset.range 13, stT254 (i+1)) + stT254 14 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 13
    simpa using h
  have hprev := st254_p13
  have hstep := st254_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p15 : ((18267716210883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT254 (i+1))
      = (∑ i ∈ Finset.range 14, stT254 (i+1)) + stT254 15 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 14
    simpa using h
  have hprev := st254_p14
  have hstep := st254_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p16 : ((20458216210883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT254 (i+1))
      = (∑ i ∈ Finset.range 15, stT254 (i+1)) + stT254 16 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 15
    simpa using h
  have hprev := st254_p15
  have hstep := st254_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p17 : ((4519495744467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT254 (i+1))
      = (∑ i ∈ Finset.range 16, stT254 (i+1)) + stT254 17 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 16
    simpa using h
  have hprev := st254_p16
  have hstep := st254_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p18 : ((9679376688669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT254 (i+1))
      = (∑ i ∈ Finset.range 17, stT254 (i+1)) + stT254 18 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 17
    simpa using h
  have hprev := st254_p17
  have hstep := st254_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p19 : ((21619560217029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT254 (i+1))
      = (∑ i ∈ Finset.range 18, stT254 (i+1)) + stT254 19 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 18
    simpa using h
  have hprev := st254_p18
  have hstep := st254_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p20 : ((11711441703293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT254 (i+1))
      = (∑ i ∈ Finset.range 19, stT254 (i+1)) + stT254 20 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 19
    simpa using h
  have hprev := st254_p19
  have hstep := st254_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p21 : ((1268959535417/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT254 (i+1))
      = (∑ i ∈ Finset.range 20, stT254 (i+1)) + stT254 21 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 20
    simpa using h
  have hprev := st254_p20
  have hstep := st254_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p22 : ((27421212088891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT254 (i+1))
      = (∑ i ∈ Finset.range 21, stT254 (i+1)) + stT254 22 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 21
    simpa using h
  have hprev := st254_p21
  have hstep := st254_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p23 : ((43886403499/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT254 (i+1))
      = (∑ i ∈ Finset.range 22, stT254 (i+1)) + stT254 23 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 22
    simpa using h
  have hprev := st254_p22
  have hstep := st254_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p24 : ((25421242679401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT254 (i+1))
      = (∑ i ∈ Finset.range 23, stT254 (i+1)) + stT254 24 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 23
    simpa using h
  have hprev := st254_p23
  have hstep := st254_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p25 : ((26867558679401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT254 (i+1))
      = (∑ i ∈ Finset.range 24, stT254 (i+1)) + stT254 25 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 24
    simpa using h
  have hprev := st254_p24
  have hstep := st254_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p26 : ((26342171224249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT254 (i+1))
      = (∑ i ∈ Finset.range 25, stT254 (i+1)) + stT254 26 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 25
    simpa using h
  have hprev := st254_p25
  have hstep := st254_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p27 : ((26553148385749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT254 (i+1))
      = (∑ i ∈ Finset.range 26, stT254 (i+1)) + stT254 27 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 26
    simpa using h
  have hprev := st254_p26
  have hstep := st254_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p28 : ((812483907863/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT254 (i+1))
      = (∑ i ∈ Finset.range 27, stT254 (i+1)) + stT254 28 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 27
    simpa using h
  have hprev := st254_p27
  have hstep := st254_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p29 : ((854465901287/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT254 (i+1))
      = (∑ i ∈ Finset.range 28, stT254 (i+1)) + stT254 29 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 28
    simpa using h
  have hprev := st254_p28
  have hstep := st254_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p30 : ((12759765588537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT254 (i+1))
      = (∑ i ∈ Finset.range 29, stT254 (i+1)) + stT254 30 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 29
    simpa using h
  have hprev := st254_p29
  have hstep := st254_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p31 : ((26256363716377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT254 (i+1))
      = (∑ i ∈ Finset.range 30, stT254 (i+1)) + stT254 31 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 30
    simpa using h
  have hprev := st254_p30
  have hstep := st254_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p32 : ((5536315464839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT254 (i+1))
      = (∑ i ∈ Finset.range 31, stT254 (i+1)) + stT254 32 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 31
    simpa using h
  have hprev := st254_p31
  have hstep := st254_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p33 : ((5341160436923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT254 (i+1))
      = (∑ i ∈ Finset.range 32, stT254 (i+1)) + stT254 33 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 32
    simpa using h
  have hprev := st254_p32
  have hstep := st254_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p34 : ((25079774223421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT254 (i+1))
      = (∑ i ∈ Finset.range 33, stT254 (i+1)) + stT254 34 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 33
    simpa using h
  have hprev := st254_p33
  have hstep := st254_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p35 : ((12398943231209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT254 (i+1))
      = (∑ i ∈ Finset.range 34, stT254 (i+1)) + stT254 35 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 34
    simpa using h
  have hprev := st254_p34
  have hstep := st254_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p36 : ((12938754681951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT254 (i+1))
      = (∑ i ∈ Finset.range 35, stT254 (i+1)) + stT254 36 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 35
    simpa using h
  have hprev := st254_p35
  have hstep := st254_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p37 : ((27491858886221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT254 (i+1))
      = (∑ i ∈ Finset.range 36, stT254 (i+1)) + stT254 37 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 36
    simpa using h
  have hprev := st254_p36
  have hstep := st254_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p38 : ((5808247419967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT254 (i+1))
      = (∑ i ∈ Finset.range 37, stT254 (i+1)) + stT254 38 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 37
    simpa using h
  have hprev := st254_p37
  have hstep := st254_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p39 : ((30348839961873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT254 (i+1))
      = (∑ i ∈ Finset.range 38, stT254 (i+1)) + stT254 39 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 38
    simpa using h
  have hprev := st254_p38
  have hstep := st254_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p40 : ((31491822486141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT254 (i+1))
      = (∑ i ∈ Finset.range 39, stT254 (i+1)) + stT254 40 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 39
    simpa using h
  have hprev := st254_p39
  have hstep := st254_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p41 : ((8158215864573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT254 (i+1))
      = (∑ i ∈ Finset.range 40, stT254 (i+1)) + stT254 41 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 40
    simpa using h
  have hprev := st254_p40
  have hstep := st254_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p42 : ((33915733379327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT254 (i+1))
      = (∑ i ∈ Finset.range 41, stT254 (i+1)) + stT254 42 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 41
    simpa using h
  have hprev := st254_p41
  have hstep := st254_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p43 : ((35380127675307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT254 (i+1))
      = (∑ i ∈ Finset.range 42, stT254 (i+1)) + stT254 43 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 42
    simpa using h
  have hprev := st254_p42
  have hstep := st254_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p44 : ((36868064341523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT254 (i+1))
      = (∑ i ∈ Finset.range 43, stT254 (i+1)) + stT254 44 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 43
    simpa using h
  have hprev := st254_p43
  have hstep := st254_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p45 : ((37972552991377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT254 (i+1))
      = (∑ i ∈ Finset.range 44, stT254 (i+1)) + stT254 45 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 44
    simpa using h
  have hprev := st254_p44
  have hstep := st254_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p46 : ((38169402672067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT254 (i+1))
      = (∑ i ∈ Finset.range 45, stT254 (i+1)) + stT254 46 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 45
    simpa using h
  have hprev := st254_p45
  have hstep := st254_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p47 : ((37244647745067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT254 (i+1))
      = (∑ i ∈ Finset.range 46, stT254 (i+1)) + stT254 47 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 46
    simpa using h
  have hprev := st254_p46
  have hstep := st254_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p48 : ((7160621832543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT254 (i+1))
      = (∑ i ∈ Finset.range 47, stT254 (i+1)) + stT254 48 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 47
    simpa using h
  have hprev := st254_p47
  have hstep := st254_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p49 : ((35151681759287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT254 (i+1))
      = (∑ i ∈ Finset.range 48, stT254 (i+1)) + stT254 49 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 48
    simpa using h
  have hprev := st254_p48
  have hstep := st254_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p50 : ((3603891798331/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT254 (i+1))
      = (∑ i ∈ Finset.range 49, stT254 (i+1)) + stT254 50 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 49
    simpa using h
  have hprev := st254_p49
  have hstep := st254_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p51 : ((3734898774487/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT254 (i+1))
      = (∑ i ∈ Finset.range 50, stT254 (i+1)) + stT254 51 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 50
    simpa using h
  have hprev := st254_p50
  have hstep := st254_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p52 : ((3715409375933/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT254 (i+1))
      = (∑ i ∈ Finset.range 51, stT254 (i+1)) + stT254 52 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 51
    simpa using h
  have hprev := st254_p51
  have hstep := st254_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p53 : ((17890287835057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT254 (i+1))
      = (∑ i ∈ Finset.range 52, stT254 (i+1)) + stT254 53 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 52
    simpa using h
  have hprev := st254_p52
  have hstep := st254_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p54 : ((17876440729743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT254 (i+1))
      = (∑ i ∈ Finset.range 53, stT254 (i+1)) + stT254 54 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 53
    simpa using h
  have hprev := st254_p53
  have hstep := st254_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p55 : ((37100548278829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT254 (i+1))
      = (∑ i ∈ Finset.range 54, stT254 (i+1)) + stT254 55 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 54
    simpa using h
  have hprev := st254_p54
  have hstep := st254_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p56 : ((9219553714119/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT254 (i+1))
      = (∑ i ∈ Finset.range 55, stT254 (i+1)) + stT254 56 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 55
    simpa using h
  have hprev := st254_p55
  have hstep := st254_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p57 : ((4456246925697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT254 (i+1))
      = (∑ i ∈ Finset.range 56, stT254 (i+1)) + stT254 57 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 56
    simpa using h
  have hprev := st254_p56
  have hstep := st254_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p58 : ((569909294841/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT254 (i+1))
      = (∑ i ∈ Finset.range 57, stT254 (i+1)) + stT254 58 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 57
    simpa using h
  have hprev := st254_p57
  have hstep := st254_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p59 : ((2320184512269/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT254 (i+1))
      = (∑ i ∈ Finset.range 58, stT254 (i+1)) + stT254 59 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 58
    simpa using h
  have hprev := st254_p58
  have hstep := st254_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p60 : ((4479481354653/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT254 (i+1))
      = (∑ i ∈ Finset.range 59, stT254 (i+1)) + stT254 60 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 59
    simpa using h
  have hprev := st254_p59
  have hstep := st254_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p61 : ((4547007802927/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT254 (i+1))
      = (∑ i ∈ Finset.range 60, stT254 (i+1)) + stT254 61 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 60
    simpa using h
  have hprev := st254_p60
  have hstep := st254_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p62 : ((18521506804287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT254 (i+1))
      = (∑ i ∈ Finset.range 61, stT254 (i+1)) + stT254 62 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 61
    simpa using h
  have hprev := st254_p61
  have hstep := st254_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p63 : ((17894394239377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT254 (i+1))
      = (∑ i ∈ Finset.range 62, stT254 (i+1)) + stT254 63 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 62
    simpa using h
  have hprev := st254_p62
  have hstep := st254_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p64 : ((18346027989377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT254 (i+1))
      = (∑ i ∈ Finset.range 63, stT254 (i+1)) + stT254 64 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 63
    simpa using h
  have hprev := st254_p63
  have hstep := st254_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p65 : ((18339066536227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT254 (i+1))
      = (∑ i ∈ Finset.range 64, stT254 (i+1)) + stT254 65 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 64
    simpa using h
  have hprev := st254_p64
  have hstep := st254_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p66 : ((8965411249121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT254 (i+1))
      = (∑ i ∈ Finset.range 65, stT254 (i+1)) + stT254 66 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 65
    simpa using h
  have hprev := st254_p65
  have hstep := st254_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p67 : ((9266540494711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT254 (i+1))
      = (∑ i ∈ Finset.range 66, stT254 (i+1)) + stT254 67 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 66
    simpa using h
  have hprev := st254_p66
  have hstep := st254_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p68 : ((35976190328817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT254 (i+1))
      = (∑ i ∈ Finset.range 67, stT254 (i+1)) + stT254 68 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 67
    simpa using h
  have hprev := st254_p67
  have hstep := st254_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p69 : ((36605818897539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT254 (i+1))
      = (∑ i ∈ Finset.range 68, stT254 (i+1)) + stT254 69 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 68
    simpa using h
  have hprev := st254_p68
  have hstep := st254_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p70 : ((36561189046679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT254 (i+1))
      = (∑ i ∈ Finset.range 69, stT254 (i+1)) + stT254 70 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 69
    simpa using h
  have hprev := st254_p69
  have hstep := st254_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p71 : ((7214575857061/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT254 (i+1))
      = (∑ i ∈ Finset.range 70, stT254 (i+1)) + stT254 71 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 70
    simpa using h
  have hprev := st254_p70
  have hstep := st254_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p72 : ((36946386924461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT254 (i+1))
      = (∑ i ∈ Finset.range 71, stT254 (i+1)) + stT254 72 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 71
    simpa using h
  have hprev := st254_p71
  have hstep := st254_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p73 : ((35856808258829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT254 (i+1))
      = (∑ i ∈ Finset.range 72, stT254 (i+1)) + stT254 73 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 72
    simpa using h
  have hprev := st254_p72
  have hstep := st254_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p74 : ((7403430455569/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT254 (i+1))
      = (∑ i ∈ Finset.range 73, stT254 (i+1)) + stT254 74 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 73
    simpa using h
  have hprev := st254_p73
  have hstep := st254_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p75 : ((17943657727239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT254 (i+1))
      = (∑ i ∈ Finset.range 74, stT254 (i+1)) + stT254 75 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 74
    simpa using h
  have hprev := st254_p74
  have hstep := st254_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p76 : ((2308094828751/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT254 (i+1))
      = (∑ i ∈ Finset.range 75, stT254 (i+1)) + stT254 76 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 75
    simpa using h
  have hprev := st254_p75
  have hstep := st254_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p77 : ((17997544671537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT254 (i+1))
      = (∑ i ∈ Finset.range 76, stT254 (i+1)) + stT254 77 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 76
    simpa using h
  have hprev := st254_p76
  have hstep := st254_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p78 : ((9206758599483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT254 (i+1))
      = (∑ i ∈ Finset.range 77, stT254 (i+1)) + stT254 78 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 77
    simpa using h
  have hprev := st254_p77
  have hstep := st254_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p79 : ((9018907719019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT254 (i+1))
      = (∑ i ∈ Finset.range 78, stT254 (i+1)) + stT254 79 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 78
    simpa using h
  have hprev := st254_p78
  have hstep := st254_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p80 : ((9194177280297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT254 (i+1))
      = (∑ i ∈ Finset.range 79, stT254 (i+1)) + stT254 80 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 79
    simpa using h
  have hprev := st254_p79
  have hstep := st254_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p81 : ((9022950476649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT254 (i+1))
      = (∑ i ∈ Finset.range 80, stT254 (i+1)) + stT254 81 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 80
    simpa using h
  have hprev := st254_p80
  have hstep := st254_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p82 : ((36793924279281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT254 (i+1))
      = (∑ i ∈ Finset.range 81, stT254 (i+1)) + stT254 82 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 81
    simpa using h
  have hprev := st254_p81
  have hstep := st254_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p83 : ((7208835406569/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT254 (i+1))
      = (∑ i ∈ Finset.range 82, stT254 (i+1)) + stT254 83 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 82
    simpa using h
  have hprev := st254_p82
  have hstep := st254_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p84 : ((7372985382263/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT254 (i+1))
      = (∑ i ∈ Finset.range 83, stT254 (i+1)) + stT254 84 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 83
    simpa using h
  have hprev := st254_p83
  have hstep := st254_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p85 : ((17979884941163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT254 (i+1))
      = (∑ i ∈ Finset.range 84, stT254 (i+1)) + stT254 85 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 84
    simpa using h
  have hprev := st254_p84
  have hstep := st254_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p86 : ((36947451636379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT254 (i+1))
      = (∑ i ∈ Finset.range 85, stT254 (i+1)) + stT254 86 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 85
    simpa using h
  have hprev := st254_p85
  have hstep := st254_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p87 : ((35898329027551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT254 (i+1))
      = (∑ i ∈ Finset.range 86, stT254 (i+1)) + stT254 87 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 86
    simpa using h
  have hprev := st254_p86
  have hstep := st254_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p88 : ((36963767045961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT254 (i+1))
      = (∑ i ∈ Finset.range 87, stT254 (i+1)) + stT254 88 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 87
    simpa using h
  have hprev := st254_p87
  have hstep := st254_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p89 : ((35951850555241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT254 (i+1))
      = (∑ i ∈ Finset.range 88, stT254 (i+1)) + stT254 89 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 88
    simpa using h
  have hprev := st254_p88
  have hstep := st254_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p90 : ((36818136037693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT254 (i+1))
      = (∑ i ∈ Finset.range 89, stT254 (i+1)) + stT254 90 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 89
    simpa using h
  have hprev := st254_p89
  have hstep := st254_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p91 : ((9050170636247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT254 (i+1))
      = (∑ i ∈ Finset.range 90, stT254 (i+1)) + stT254 91 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 90
    simpa using h
  have hprev := st254_p90
  have hstep := st254_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p92 : ((4559105615377/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT254 (i+1))
      = (∑ i ∈ Finset.range 91, stT254 (i+1)) + stT254 92 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 91
    simpa using h
  have hprev := st254_p91
  have hstep := st254_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p93 : ((36608721797301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT254 (i+1))
      = (∑ i ∈ Finset.range 92, stT254 (i+1)) + stT254 93 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 92
    simpa using h
  have hprev := st254_p92
  have hstep := st254_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p94 : ((36063898911351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT254 (i+1))
      = (∑ i ∈ Finset.range 93, stT254 (i+1)) + stT254 94 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 93
    simpa using h
  have hprev := st254_p93
  have hstep := st254_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p95 : ((36932781211947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT254 (i+1))
      = (∑ i ∈ Finset.range 94, stT254 (i+1)) + stT254 95 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 94
    simpa using h
  have hprev := st254_p94
  have hstep := st254_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p96 : ((17957635022067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT254 (i+1))
      = (∑ i ∈ Finset.range 95, stT254 (i+1)) + stT254 96 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 95
    simpa using h
  have hprev := st254_p95
  have hstep := st254_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p97 : ((4604728835077/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT254 (i+1))
      = (∑ i ∈ Finset.range 96, stT254 (i+1)) + stT254 97 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 96
    simpa using h
  have hprev := st254_p96
  have hstep := st254_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p98 : ((36264375913893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT254 (i+1))
      = (∑ i ∈ Finset.range 97, stT254 (i+1)) + stT254 98 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 97
    simpa using h
  have hprev := st254_p97
  have hstep := st254_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p99 : ((36305274889571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT254 (i+1))
      = (∑ i ∈ Finset.range 98, stT254 (i+1)) + stT254 99 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 98
    simpa using h
  have hprev := st254_p98
  have hstep := st254_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p100 : ((36826258368587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT254 (i+1))
      = (∑ i ∈ Finset.range 99, stT254 (i+1)) + stT254 100 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 99
    simpa using h
  have hprev := st254_p99
  have hstep := st254_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p101 : ((35913062244087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT254 (i+1))
      = (∑ i ∈ Finset.range 100, stT254 (i+1)) + stT254 101 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 100
    simpa using h
  have hprev := st254_p100
  have hstep := st254_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p102 : ((36876958466823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT254 (i+1))
      = (∑ i ∈ Finset.range 101, stT254 (i+1)) + stT254 102 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 101
    simpa using h
  have hprev := st254_p101
  have hstep := st254_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p103 : ((36259880774373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT254 (i+1))
      = (∑ i ∈ Finset.range 102, stT254 (i+1)) + stT254 103 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 102
    simpa using h
  have hprev := st254_p102
  have hstep := st254_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p104 : ((18124630050781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT254 (i+1))
      = (∑ i ∈ Finset.range 103, stT254 (i+1)) + stT254 104 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 103
    simpa using h
  have hprev := st254_p103
  have hstep := st254_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p105 : ((18446983483381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT254 (i+1))
      = (∑ i ∈ Finset.range 104, stT254 (i+1)) + stT254 105 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 104
    simpa using h
  have hprev := st254_p104
  have hstep := st254_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p106 : ((17964528244033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT254 (i+1))
      = (∑ i ∈ Finset.range 105, stT254 (i+1)) + stT254 106 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 105
    simpa using h
  have hprev := st254_p105
  have hstep := st254_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p107 : ((18351774650289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT254 (i+1))
      = (∑ i ∈ Finset.range 106, stT254 (i+1)) + stT254 107 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 106
    simpa using h
  have hprev := st254_p106
  have hstep := st254_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p108 : ((36559226084343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT254 (i+1))
      = (∑ i ∈ Finset.range 107, stT254 (i+1)) + stT254 108 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 107
    simpa using h
  have hprev := st254_p107
  have hstep := st254_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p109 : ((17989729095189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT254 (i+1))
      = (∑ i ∈ Finset.range 108, stT254 (i+1)) + stT254 109 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 108
    simpa using h
  have hprev := st254_p108
  have hstep := st254_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p110 : ((9232056097507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT254 (i+1))
      = (∑ i ∈ Finset.range 109, stT254 (i+1)) + stT254 110 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 109
    simpa using h
  have hprev := st254_p109
  have hstep := st254_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p111 : ((18114952560239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT254 (i+1))
      = (∑ i ∈ Finset.range 110, stT254 (i+1)) + stT254 111 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 110
    simpa using h
  have hprev := st254_p110
  have hstep := st254_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p112 : ((18097496728407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT254 (i+1))
      = (∑ i ∈ Finset.range 111, stT254 (i+1)) + stT254 112 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 111
    simpa using h
  have hprev := st254_p111
  have hstep := st254_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p113 : ((18471889647967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT254 (i+1))
      = (∑ i ∈ Finset.range 112, stT254 (i+1)) + stT254 113 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 112
    simpa using h
  have hprev := st254_p112
  have hstep := st254_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p114 : ((1126159415521/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT254 (i+1))
      = (∑ i ∈ Finset.range 113, stT254 (i+1)) + stT254 114 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 113
    simpa using h
  have hprev := st254_p113
  have hstep := st254_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p115 : ((4549375124299/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT254 (i+1))
      = (∑ i ∈ Finset.range 114, stT254 (i+1)) + stT254 115 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 114
    simpa using h
  have hprev := st254_p114
  have hstep := st254_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p116 : ((4609882976743/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT254 (i+1))
      = (∑ i ∈ Finset.range 115, stT254 (i+1)) + stT254 116 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 115
    simpa using h
  have hprev := st254_p115
  have hstep := st254_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p117 : ((17978118080377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT254 (i+1))
      = (∑ i ∈ Finset.range 116, stT254 (i+1)) + stT254 117 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 116
    simpa using h
  have hprev := st254_p116
  have hstep := st254_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p118 : ((4564339063021/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT254 (i+1))
      = (∑ i ∈ Finset.range 117, stT254 (i+1)) + stT254 118 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 117
    simpa using h
  have hprev := st254_p117
  have hstep := st254_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p119 : ((18412871776039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT254 (i+1))
      = (∑ i ∈ Finset.range 118, stT254 (i+1)) + stT254 119 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 118
    simpa using h
  have hprev := st254_p118
  have hstep := st254_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p120 : ((2245787709117/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT254 (i+1))
      = (∑ i ∈ Finset.range 119, stT254 (i+1)) + stT254 120 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 119
    simpa using h
  have hprev := st254_p119
  have hstep := st254_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p121 : ((18274658182761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT254 (i+1))
      = (∑ i ∈ Finset.range 120, stT254 (i+1)) + stT254 121 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 120
    simpa using h
  have hprev := st254_p120
  have hstep := st254_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p122 : ((7364300397729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT254 (i+1))
      = (∑ i ∈ Finset.range 121, stT254 (i+1)) + stT254 122 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 121
    simpa using h
  have hprev := st254_p121
  have hstep := st254_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p123 : ((57499638229/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT254 (i+1))
      = (∑ i ∈ Finset.range 122, stT254 (i+1)) + stT254 123 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 122
    simpa using h
  have hprev := st254_p122
  have hstep := st254_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p124 : ((36504104312221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT254 (i+1))
      = (∑ i ∈ Finset.range 123, stT254 (i+1)) + stT254 124 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 123
    simpa using h
  have hprev := st254_p123
  have hstep := st254_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p125 : ((36867345427753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT254 (i+1))
      = (∑ i ∈ Finset.range 124, stT254 (i+1)) + stT254 125 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 124
    simpa using h
  have hprev := st254_p124
  have hstep := st254_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p126 : ((35976971533771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT254 (i+1))
      = (∑ i ∈ Finset.range 125, stT254 (i+1)) + stT254 126 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 125
    simpa using h
  have hprev := st254_p125
  have hstep := st254_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p127 : ((36380356472523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT254 (i+1))
      = (∑ i ∈ Finset.range 126, stT254 (i+1)) + stT254 127 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 126
    simpa using h
  have hprev := st254_p126
  have hstep := st254_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p128 : ((18467168164977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT254 (i+1))
      = (∑ i ∈ Finset.range 127, stT254 (i+1)) + stT254 128 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 127
    simpa using h
  have hprev := st254_p127
  have hstep := st254_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p129 : ((9021527018913/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT254 (i+1))
      = (∑ i ∈ Finset.range 128, stT254 (i+1)) + stT254 129 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 128
    simpa using h
  have hprev := st254_p128
  have hstep := st254_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p130 : ((2261888099869/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT254 (i+1))
      = (∑ i ∈ Finset.range 129, stT254 (i+1)) + stT254 130 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 129
    simpa using h
  have hprev := st254_p129
  have hstep := st254_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p131 : ((1154973804079/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT254 (i+1))
      = (∑ i ∈ Finset.range 130, stT254 (i+1)) + stT254 131 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 130
    simpa using h
  have hprev := st254_p130
  have hstep := st254_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p132 : ((9075533231719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT254 (i+1))
      = (∑ i ∈ Finset.range 131, stT254 (i+1)) + stT254 132 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 131
    simpa using h
  have hprev := st254_p131
  have hstep := st254_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p133 : ((8997288693759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT254 (i+1))
      = (∑ i ∈ Finset.range 132, stT254 (i+1)) + stT254 133 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 132
    simpa using h
  have hprev := st254_p132
  have hstep := st254_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p134 : ((2303273483619/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT254 (i+1))
      = (∑ i ∈ Finset.range 133, stT254 (i+1)) + stT254 134 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 133
    simpa using h
  have hprev := st254_p133
  have hstep := st254_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p135 : ((3661424922039/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT254 (i+1))
      = (∑ i ∈ Finset.range 134, stT254 (i+1)) + stT254 135 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 134
    simpa using h
  have hprev := st254_p134
  have hstep := st254_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p136 : ((17949423120231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT254 (i+1))
      = (∑ i ∈ Finset.range 135, stT254 (i+1)) + stT254 136 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 135
    simpa using h
  have hprev := st254_p135
  have hstep := st254_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p137 : ((1827702374881/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT254 (i+1))
      = (∑ i ∈ Finset.range 136, stT254 (i+1)) + stT254 137 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 136
    simpa using h
  have hprev := st254_p136
  have hstep := st254_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p138 : ((9225329132891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT254 (i+1))
      = (∑ i ∈ Finset.range 137, stT254 (i+1)) + stT254 138 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 137
    simpa using h
  have hprev := st254_p137
  have hstep := st254_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p139 : ((36063530569649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT254 (i+1))
      = (∑ i ∈ Finset.range 138, stT254 (i+1)) + stT254 139 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 138
    simpa using h
  have hprev := st254_p138
  have hstep := st254_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p140 : ((36141891558221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT254 (i+1))
      = (∑ i ∈ Finset.range 139, stT254 (i+1)) + stT254 140 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 139
    simpa using h
  have hprev := st254_p139
  have hstep := st254_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p141 : ((9234645180197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT254 (i+1))
      = (∑ i ∈ Finset.range 140, stT254 (i+1)) + stT254 141 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 140
    simpa using h
  have hprev := st254_p140
  have hstep := st254_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p142 : ((18248455001593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT254 (i+1))
      = (∑ i ∈ Finset.range 141, stT254 (i+1)) + stT254 142 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 141
    simpa using h
  have hprev := st254_p141
  have hstep := st254_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p143 : ((35894121797739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT254 (i+1))
      = (∑ i ∈ Finset.range 142, stT254 (i+1)) + stT254 143 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 142
    simpa using h
  have hprev := st254_p142
  have hstep := st254_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p144 : ((18289583678527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT254 (i+1))
      = (∑ i ∈ Finset.range 143, stT254 (i+1)) + stT254 144 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 143
    simpa using h
  have hprev := st254_p143
  have hstep := st254_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p145 : ((4614594505381/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT254 (i+1))
      = (∑ i ∈ Finset.range 144, stT254 (i+1)) + stT254 145 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 144
    simpa using h
  have hprev := st254_p144
  have hstep := st254_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p146 : ((9028394001633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT254 (i+1))
      = (∑ i ∈ Finset.range 145, stT254 (i+1)) + stT254 146 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 145
    simpa using h
  have hprev := st254_p145
  have hstep := st254_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p147 : ((3604697775543/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT254 (i+1))
      = (∑ i ∈ Finset.range 146, stT254 (i+1)) + stT254 147 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 146
    simpa using h
  have hprev := st254_p146
  have hstep := st254_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p148 : ((18433445233311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT254 (i+1))
      = (∑ i ∈ Finset.range 147, stT254 (i+1)) + stT254 148 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 147
    simpa using h
  have hprev := st254_p147
  have hstep := st254_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p149 : ((3669596917907/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT254 (i+1))
      = (∑ i ∈ Finset.range 148, stT254 (i+1)) + stT254 149 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 148
    simpa using h
  have hprev := st254_p148
  have hstep := st254_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p150 : ((4490714208771/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT254 (i+1))
      = (∑ i ∈ Finset.range 149, stT254 (i+1)) + stT254 150 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 149
    simpa using h
  have hprev := st254_p149
  have hstep := st254_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p151 : ((4535435114523/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT254 (i+1))
      = (∑ i ∈ Finset.range 150, stT254 (i+1)) + stT254 151 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 150
    simpa using h
  have hprev := st254_p150
  have hstep := st254_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p152 : ((36970211957697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT254 (i+1))
      = (∑ i ∈ Finset.range 151, stT254 (i+1)) + stT254 152 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 151
    simpa using h
  have hprev := st254_p151
  have hstep := st254_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p153 : ((18238588043597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT254 (i+1))
      = (∑ i ∈ Finset.range 152, stT254 (i+1)) + stT254 153 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 152
    simpa using h
  have hprev := st254_p152
  have hstep := st254_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p154 : ((35881923501147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT254 (i+1))
      = (∑ i ∈ Finset.range 153, stT254 (i+1)) + stT254 154 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 153
    simpa using h
  have hprev := st254_p153
  have hstep := st254_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p155 : ((1139540143539/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT254 (i+1))
      = (∑ i ∈ Finset.range 154, stT254 (i+1)) + stT254 155 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 154
    simpa using h
  have hprev := st254_p154
  have hstep := st254_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p156 : ((1155564752979/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT254 (i+1))
      = (∑ i ∈ Finset.range 155, stT254 (i+1)) + stT254 156 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 155
    simpa using h
  have hprev := st254_p155
  have hstep := st254_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p157 : ((36339306405051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT254 (i+1))
      = (∑ i ∈ Finset.range 156, stT254 (i+1)) + stT254 157 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 156
    simpa using h
  have hprev := st254_p156
  have hstep := st254_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p158 : ((35889361871433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT254 (i+1))
      = (∑ i ∈ Finset.range 157, stT254 (i+1)) + stT254 158 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 157
    simpa using h
  have hprev := st254_p157
  have hstep := st254_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p159 : ((18278640659699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT254 (i+1))
      = (∑ i ∈ Finset.range 158, stT254 (i+1)) + stT254 159 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 158
    simpa using h
  have hprev := st254_p158
  have hstep := st254_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p160 : ((4621109011949/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT254 (i+1))
      = (∑ i ∈ Finset.range 159, stT254 (i+1)) + stT254 160 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 159
    simpa using h
  have hprev := st254_p159
  have hstep := st254_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p161 : ((567050059667/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT254 (i+1))
      = (∑ i ∈ Finset.range 160, stT254 (i+1)) + stT254 161 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 160
    simpa using h
  have hprev := st254_p160
  have hstep := st254_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p162 : ((17945662549669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT254 (i+1))
      = (∑ i ∈ Finset.range 161, stT254 (i+1)) + stT254 162 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 161
    simpa using h
  have hprev := st254_p161
  have hstep := st254_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p163 : ((18281219749529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT254 (i+1))
      = (∑ i ∈ Finset.range 162, stT254 (i+1)) + stT254 163 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 162
    simpa using h
  have hprev := st254_p162
  have hstep := st254_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p164 : ((18488231760669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT254 (i+1))
      = (∑ i ∈ Finset.range 163, stT254 (i+1)) + stT254 164 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 163
    simpa using h
  have hprev := st254_p163
  have hstep := st254_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p165 : ((9081913667437/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT254 (i+1))
      = (∑ i ∈ Finset.range 164, stT254 (i+1)) + stT254 165 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 164
    simpa using h
  have hprev := st254_p164
  have hstep := st254_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p166 : ((2242223609893/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT254 (i+1))
      = (∑ i ∈ Finset.range 165, stT254 (i+1)) + stT254 166 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 165
    simpa using h
  have hprev := st254_p165
  have hstep := st254_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p167 : ((18241773637349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT254 (i+1))
      = (∑ i ∈ Finset.range 166, stT254 (i+1)) + stT254 167 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 166
    simpa using h
  have hprev := st254_p166
  have hstep := st254_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p168 : ((3699300397801/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT254 (i+1))
      = (∑ i ∈ Finset.range 167, stT254 (i+1)) + stT254 168 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 167
    simpa using h
  have hprev := st254_p167
  have hstep := st254_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p169 : ((36448649199319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT254 (i+1))
      = (∑ i ∈ Finset.range 168, stT254 (i+1)) + stT254 169 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 168
    simpa using h
  have hprev := st254_p168
  have hstep := st254_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p170 : ((35868897287959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT254 (i+1))
      = (∑ i ∈ Finset.range 169, stT254 (i+1)) + stT254 170 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 169
    simpa using h
  have hprev := st254_p169
  have hstep := st254_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p171 : ((18160551963631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT254 (i+1))
      = (∑ i ∈ Finset.range 170, stT254 (i+1)) + stT254 171 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 170
    simpa using h
  have hprev := st254_p170
  have hstep := st254_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p172 : ((18486935520493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT254 (i+1))
      = (∑ i ∈ Finset.range 171, stT254 (i+1)) + stT254 172 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 171
    simpa using h
  have hprev := st254_p171
  have hstep := st254_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p173 : ((2290423087111/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT254 (i+1))
      = (∑ i ∈ Finset.range 172, stT254 (i+1)) + stT254 173 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 172
    simpa using h
  have hprev := st254_p172
  have hstep := st254_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p174 : ((7186299232877/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT254 (i+1))
      = (∑ i ∈ Finset.range 173, stT254 (i+1)) + stT254 174 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 173
    simpa using h
  have hprev := st254_p173
  have hstep := st254_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p175 : ((36098402799001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT254 (i+1))
      = (∑ i ∈ Finset.range 174, stT254 (i+1)) + stT254 175 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 174
    simpa using h
  have hprev := st254_p174
  have hstep := st254_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p176 : ((36848439045009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT254 (i+1))
      = (∑ i ∈ Finset.range 175, stT254 (i+1)) + stT254 176 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 175
    simpa using h
  have hprev := st254_p175
  have hstep := st254_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p177 : ((36872829206063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT254 (i+1))
      = (∑ i ∈ Finset.range 176, stT254 (i+1)) + stT254 177 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 176
    simpa using h
  have hprev := st254_p176
  have hstep := st254_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p178 : ((36134360298383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT254 (i+1))
      = (∑ i ∈ Finset.range 177, stT254 (i+1)) + stT254 178 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 177
    simpa using h
  have hprev := st254_p177
  have hstep := st254_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p179 : ((35899113039179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT254 (i+1))
      = (∑ i ∈ Finset.range 178, stT254 (i+1)) + stT254 179 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 178
    simpa using h
  have hprev := st254_p178
  have hstep := st254_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p180 : ((9140402662651/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT254 (i+1))
      = (∑ i ∈ Finset.range 179, stT254 (i+1)) + stT254 180 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 179
    simpa using h
  have hprev := st254_p179
  have hstep := st254_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p181 : ((18502576381377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT254 (i+1))
      = (∑ i ∈ Finset.range 180, stT254 (i+1)) + stT254 181 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 180
    simpa using h
  have hprev := st254_p180
  have hstep := st254_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p182 : ((18247236511377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT254 (i+1))
      = (∑ i ∈ Finset.range 181, stT254 (i+1)) + stT254 182 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 181
    simpa using h
  have hprev := st254_p181
  have hstep := st254_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p183 : ((7007127547/1953125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT254 (i+1))
      = (∑ i ∈ Finset.range 182, stT254 (i+1)) + stT254 183 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 182
    simpa using h
  have hprev := st254_p182
  have hstep := st254_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p184 : ((4519963143469/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT254 (i+1))
      = (∑ i ∈ Finset.range 183, stT254 (i+1)) + stT254 184 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 183
    simpa using h
  have hprev := st254_p183
  have hstep := st254_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p185 : ((18440093832417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT254 (i+1))
      = (∑ i ∈ Finset.range 184, stT254 (i+1)) + stT254 185 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 184
    simpa using h
  have hprev := st254_p184
  have hstep := st254_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p186 : ((36881077078889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT254 (i+1))
      = (∑ i ∈ Finset.range 185, stT254 (i+1)) + stT254 186 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 185
    simpa using h
  have hprev := st254_p185
  have hstep := st254_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p187 : ((7233169934211/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT254 (i+1))
      = (∑ i ∈ Finset.range 186, stT254 (i+1)) + stT254 187 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 186
    simpa using h
  have hprev := st254_p186
  have hstep := st254_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p188 : ((3586426721963/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT254 (i+1))
      = (∑ i ∈ Finset.range 187, stT254 (i+1)) + stT254 188 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 187
    simpa using h
  have hprev := st254_p187
  have hstep := st254_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p189 : ((18221746916791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT254 (i+1))
      = (∑ i ∈ Finset.range 188, stT254 (i+1)) + stT254 189 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 188
    simpa using h
  have hprev := st254_p188
  have hstep := st254_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p190 : ((18501302564107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT254 (i+1))
      = (∑ i ∈ Finset.range 189, stT254 (i+1)) + stT254 190 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 189
    simpa using h
  have hprev := st254_p189
  have hstep := st254_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p191 : ((9171412945591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT254 (i+1))
      = (∑ i ∈ Finset.range 190, stT254 (i+1)) + stT254 191 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 190
    simpa using h
  have hprev := st254_p190
  have hstep := st254_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p192 : ((8994905381303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT254 (i+1))
      = (∑ i ∈ Finset.range 191, stT254 (i+1)) + stT254 192 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 191
    simpa using h
  have hprev := st254_p191
  have hstep := st254_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p193 : ((8987270113037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT254 (i+1))
      = (∑ i ∈ Finset.range 192, stT254 (i+1)) + stT254 193 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 192
    simpa using h
  have hprev := st254_p192
  have hstep := st254_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p194 : ((915870663713/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT254 (i+1))
      = (∑ i ∈ Finset.range 193, stT254 (i+1)) + stT254 194 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 193
    simpa using h
  have hprev := st254_p193
  have hstep := st254_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p195 : ((18509224767217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT254 (i+1))
      = (∑ i ∈ Finset.range 194, stT254 (i+1)) + stT254 195 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 194
    simpa using h
  have hprev := st254_p194
  have hstep := st254_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p196 : ((2283752414299/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT254 (i+1))
      = (∑ i ∈ Finset.range 195, stT254 (i+1)) + stT254 196 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 195
    simpa using h
  have hprev := st254_p195
  have hstep := st254_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p197 : ((35900228983719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT254 (i+1))
      = (∑ i ∈ Finset.range 196, stT254 (i+1)) + stT254 197 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 196
    simpa using h
  have hprev := st254_p196
  have hstep := st254_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p198 : ((1440843812129/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT254 (i+1))
      = (∑ i ∈ Finset.range 197, stT254 (i+1)) + stT254 198 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 197
    simpa using h
  have hprev := st254_p197
  have hstep := st254_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p199 : ((7344964547671/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT254 (i+1))
      = (∑ i ∈ Finset.range 198, stT254 (i+1)) + stT254 199 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 198
    simpa using h
  have hprev := st254_p198
  have hstep := st254_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p200 : ((37011735947597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT254 (i+1))
      = (∑ i ∈ Finset.range 199, stT254 (i+1)) + stT254 200 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 199
    simpa using h
  have hprev := st254_p199
  have hstep := st254_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p201 : ((36482258803199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT254 (i+1))
      = (∑ i ∈ Finset.range 200, stT254 (i+1)) + stT254 201 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 200
    simpa using h
  have hprev := st254_p200
  have hstep := st254_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p202 : ((35878278318833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT254 (i+1))
      = (∑ i ∈ Finset.range 201, stT254 (i+1)) + stT254 202 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 201
    simpa using h
  have hprev := st254_p201
  have hstep := st254_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p203 : ((7206590371789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT254 (i+1))
      = (∑ i ∈ Finset.range 202, stT254 (i+1)) + stT254 203 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 202
    simpa using h
  have hprev := st254_p202
  have hstep := st254_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p204 : ((7345906329409/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT254 (i+1))
      = (∑ i ∈ Finset.range 203, stT254 (i+1)) + stT254 204 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 203
    simpa using h
  have hprev := st254_p203
  have hstep := st254_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p205 : ((1480803867449/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT254 (i+1))
      = (∑ i ∈ Finset.range 204, stT254 (i+1)) + stT254 205 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 204
    simpa using h
  have hprev := st254_p204
  have hstep := st254_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p206 : ((36516923055499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT254 (i+1))
      = (∑ i ∈ Finset.range 205, stT254 (i+1)) + stT254 206 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 205
    simpa using h
  have hprev := st254_p205
  have hstep := st254_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p207 : ((35895985740271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT254 (i+1))
      = (∑ i ∈ Finset.range 206, stT254 (i+1)) + stT254 207 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 206
    simpa using h
  have hprev := st254_p206
  have hstep := st254_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p208 : ((17989278151073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT254 (i+1))
      = (∑ i ∈ Finset.range 207, stT254 (i+1)) + stT254 208 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 207
    simpa using h
  have hprev := st254_p207
  have hstep := st254_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p209 : ((71585002723/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT254 (i+1))
      = (∑ i ∈ Finset.range 208, stT254 (i+1)) + stT254 209 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 208
    simpa using h
  have hprev := st254_p208
  have hstep := st254_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p210 : ((18518141848243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT254 (i+1))
      = (∑ i ∈ Finset.range 209, stT254 (i+1)) + stT254 210 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 209
    simpa using h
  have hprev := st254_p209
  have hstep := st254_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p211 : ((18319490152861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT254 (i+1))
      = (∑ i ∈ Finset.range 210, stT254 (i+1)) + stT254 211 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 210
    simpa using h
  have hprev := st254_p210
  have hstep := st254_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p212 : ((35972698292559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT254 (i+1))
      = (∑ i ∈ Finset.range 211, stT254 (i+1)) + stT254 212 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 211
    simpa using h
  have hprev := st254_p211
  have hstep := st254_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p213 : ((35883686759947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT254 (i+1))
      = (∑ i ∈ Finset.range 212, stT254 (i+1)) + stT254 213 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 212
    simpa using h
  have hprev := st254_p212
  have hstep := st254_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p214 : ((36479809793537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT254 (i+1))
      = (∑ i ∈ Finset.range 213, stT254 (i+1)) + stT254 214 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 213
    simpa using h
  have hprev := st254_p213
  have hstep := st254_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p215 : ((7402626775099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT254 (i+1))
      = (∑ i ∈ Finset.range 214, stT254 (i+1)) + stT254 215 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 214
    simpa using h
  have hprev := st254_p214
  have hstep := st254_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p216 : ((36824604083961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT254 (i+1))
      = (∑ i ∈ Finset.range 215, stT254 (i+1)) + stT254 216 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 215
    simpa using h
  have hprev := st254_p215
  have hstep := st254_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p217 : ((36150357579991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT254 (i+1))
      = (∑ i ∈ Finset.range 216, stT254 (i+1)) + stT254 217 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 216
    simpa using h
  have hprev := st254_p216
  have hstep := st254_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p218 : ((7162773534437/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT254 (i+1))
      = (∑ i ∈ Finset.range 217, stT254 (i+1)) + stT254 218 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 217
    simpa using h
  have hprev := st254_p217
  have hstep := st254_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p219 : ((1810939646669/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT254 (i+1))
      = (∑ i ∈ Finset.range 218, stT254 (i+1)) + stT254 219 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 218
    simpa using h
  have hprev := st254_p218
  have hstep := st254_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p220 : ((36875359606933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT254 (i+1))
      = (∑ i ∈ Finset.range 219, stT254 (i+1)) + stT254 220 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 219
    simpa using h
  have hprev := st254_p219
  have hstep := st254_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p221 : ((37002280705237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT254 (i+1))
      = (∑ i ∈ Finset.range 220, stT254 (i+1)) + stT254 221 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 220
    simpa using h
  have hprev := st254_p220
  have hstep := st254_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p222 : ((36453660865669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT254 (i+1))
      = (∑ i ∈ Finset.range 221, stT254 (i+1)) + stT254 222 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 221
    simpa using h
  have hprev := st254_p221
  have hstep := st254_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p223 : ((35875044425969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT254 (i+1))
      = (∑ i ∈ Finset.range 222, stT254 (i+1)) + stT254 223 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 222
    simpa using h
  have hprev := st254_p222
  have hstep := st254_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p224 : ((17968627741823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT254 (i+1))
      = (∑ i ∈ Finset.range 223, stT254 (i+1)) + stT254 224 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 223
    simpa using h
  have hprev := st254_p223
  have hstep := st254_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p225 : ((18282180094937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT254 (i+1))
      = (∑ i ∈ Finset.range 224, stT254 (i+1)) + stT254 225 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 224
    simpa using h
  have hprev := st254_p224
  have hstep := st254_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p226 : ((18518541392447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT254 (i+1))
      = (∑ i ∈ Finset.range 225, stT254 (i+1)) + stT254 226 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 225
    simpa using h
  have hprev := st254_p225
  have hstep := st254_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p227 : ((3682139837013/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT254 (i+1))
      = (∑ i ∈ Finset.range 226, stT254 (i+1)) + stT254 227 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 226
    simpa using h
  have hprev := st254_p226
  have hstep := st254_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p228 : ((4520516766881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT254 (i+1))
      = (∑ i ∈ Finset.range 227, stT254 (i+1)) + stT254 228 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 227
    simpa using h
  have hprev := st254_p227
  have hstep := st254_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p229 : ((8950131932941/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT254 (i+1))
      = (∑ i ∈ Finset.range 228, stT254 (i+1)) + stT254 229 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 228
    simpa using h
  have hprev := st254_p228
  have hstep := st254_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p230 : ((9032627294431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT254 (i+1))
      = (∑ i ∈ Finset.range 229, stT254 (i+1)) + stT254 230 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 229
    simpa using h
  have hprev := st254_p229
  have hstep := st254_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p231 : ((4598427576893/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT254 (i+1))
      = (∑ i ∈ Finset.range 230, stT254 (i+1)) + stT254 231 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 230
    simpa using h
  have hprev := st254_p230
  have hstep := st254_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p232 : ((9263517935869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT254 (i+1))
      = (∑ i ∈ Finset.range 231, stT254 (i+1)) + stT254 232 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 231
    simpa using h
  have hprev := st254_p231
  have hstep := st254_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p233 : ((9161267804353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT254 (i+1))
      = (∑ i ∈ Finset.range 232, stT254 (i+1)) + stT254 233 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 232
    simpa using h
  have hprev := st254_p232
  have hstep := st254_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p234 : ((1125100926107/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT254 (i+1))
      = (∑ i ∈ Finset.range 233, stT254 (i+1)) + stT254 234 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 233
    simpa using h
  have hprev := st254_p233
  have hstep := st254_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p235 : ((17906319335747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT254 (i+1))
      = (∑ i ∈ Finset.range 234, stT254 (i+1)) + stT254 235 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 234
    simpa using h
  have hprev := st254_p234
  have hstep := st254_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p236 : ((18135690194723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT254 (i+1))
      = (∑ i ∈ Finset.range 235, stT254 (i+1)) + stT254 236 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 235
    simpa using h
  have hprev := st254_p235
  have hstep := st254_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p237 : ((36894658084171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT254 (i+1))
      = (∑ i ∈ Finset.range 236, stT254 (i+1)) + stT254 237 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 236
    simpa using h
  have hprev := st254_p236
  have hstep := st254_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p238 : ((37033564097853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT254 (i+1))
      = (∑ i ∈ Finset.range 237, stT254 (i+1)) + stT254 238 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 237
    simpa using h
  have hprev := st254_p237
  have hstep := st254_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p239 : ((9137001290767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT254 (i+1))
      = (∑ i ∈ Finset.range 238, stT254 (i+1)) + stT254 239 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 238
    simpa using h
  have hprev := st254_p238
  have hstep := st254_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p240 : ((17969577010511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT254 (i+1))
      = (∑ i ∈ Finset.range 239, stT254 (i+1)) + stT254 240 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 239
    simpa using h
  have hprev := st254_p239
  have hstep := st254_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p241 : ((3582637759009/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT254 (i+1))
      = (∑ i ∈ Finset.range 240, stT254 (i+1)) + stT254 241 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 240
    simpa using h
  have hprev := st254_p240
  have hstep := st254_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p242 : ((18160041567757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT254 (i+1))
      = (∑ i ∈ Finset.range 241, stT254 (i+1)) + stT254 242 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 241
    simpa using h
  have hprev := st254_p241
  have hstep := st254_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p243 : ((18461058386257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT254 (i+1))
      = (∑ i ∈ Finset.range 242, stT254 (i+1)) + stT254 243 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 242
    simpa using h
  have hprev := st254_p242
  have hstep := st254_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p244 : ((18516840819097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT254 (i+1))
      = (∑ i ∈ Finset.range 243, stT254 (i+1)) + stT254 244 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 243
    simpa using h
  have hprev := st254_p243
  have hstep := st254_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p245 : ((4568496285991/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT254 (i+1))
      = (∑ i ∈ Finset.range 244, stT254 (i+1)) + stT254 245 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 244
    simpa using h
  have hprev := st254_p244
  have hstep := st254_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p246 : ((17972121125429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT254 (i+1))
      = (∑ i ∈ Finset.range 245, stT254 (i+1)) + stT254 246 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 245
    simpa using h
  have hprev := st254_p245
  have hstep := st254_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p247 : ((17904882344339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT254 (i+1))
      = (∑ i ∈ Finset.range 246, stT254 (i+1)) + stT254 247 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 246
    simpa using h
  have hprev := st254_p246
  have hstep := st254_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p248 : ((18135561651839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT254 (i+1))
      = (∑ i ∈ Finset.range 247, stT254 (i+1)) + stT254 248 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 247
    simpa using h
  have hprev := st254_p247
  have hstep := st254_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p249 : ((18441373089589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT254 (i+1))
      = (∑ i ∈ Finset.range 248, stT254 (i+1)) + stT254 249 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 248
    simpa using h
  have hprev := st254_p248
  have hstep := st254_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_p250 : ((9265596858117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT254 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT254 (i+1))
      = (∑ i ∈ Finset.range 249, stT254 (i+1)) + stT254 250 := by
    have h := Finset.sum_range_succ (fun i => stT254 (i+1)) 249
    simpa using h
  have hprev := st254_p249
  have hstep := st254_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st254_s250 :
    |Real.sin (((254 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((563/31250 : ℚ) : ℝ))
      - ((479399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1603427/5000000) (δ := 129/10000000) (ψ := 563/31250) 254 223
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 254`** (evaluated boundary). -/
theorem station_254_sign : hardyG ((((254:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 254 250 (by norm_num) (by norm_num)
    ((563/31250 : ℚ) : ℝ)
  have hchain := st254_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT254 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((254 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((563/31250 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st254_c250
  have hsinb := abs_le.mp st254_s250
  have hbdy_lo : ((-19265357718277/322581250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((254 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((563/31250 : ℚ) : ℝ))) / 2
          - ((((254:ℕ)):ℝ))
            * Real.sin (((254 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((563/31250 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((254:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((254:ℝ) * Real.log (250:ℝ) - ((563/31250 : ℚ) : ℝ))) / 2
        - ((254:ℝ)) * Real.sin ((254:ℝ) * Real.log (250:ℝ) - ((563/31250 : ℚ) : ℝ))
        ≥ ((-243689461/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((254:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-243689461/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-243689461/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-243689461/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((254:ℕ)):ℝ))+1) * (((((254:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((11063315637/7812500000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((9265596858117/2500000000000 : ℚ) : ℝ) + ((-19265357718277/322581250000000 : ℚ) : ℝ)
      - ((11063315637/7812500000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((563/31250 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((254:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((563/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((254:ℕ)):ℝ)))).re
      - Real.sin ((563/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((254:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((254:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((254:ℕ)):ℝ))
      = (((((254:ℕ)):ℝ)) * (Real.log ((((254:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((254:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_254
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
  have hθwin : |(((563/31250 : ℚ) : ℝ) + ((55:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((254:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((254:ℕ)):ℝ)))
    (φ := ((563/31250 : ℚ) : ℝ) + ((55:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((563/31250 : ℚ) : ℝ) + ((55:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((563/31250 : ℚ)) : ℝ) - Real.pi) + ((55:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((563/31250 : ℚ)) : ℝ) - Real.pi) 55).1,
    (cos_sin_shift ((((563/31250 : ℚ)) : ℝ) - Real.pi) 55).2]
  exact cos_sin_flip ((563/31250 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_254_sign
end AxiomAudit
