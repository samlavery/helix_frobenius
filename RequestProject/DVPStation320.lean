import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 320` (rung-335.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT320 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((320 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((197137/500000 : ℚ) : ℝ))

theorem st320_c1 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((230819/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197137/2000000) (δ := 1/1000000000) (ψ := 197137/500000) 320 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t1 : ((115397/125000 : ℚ) : ℝ) ≤ stT320 1 := by
  have hc : ((115397/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115397/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((115397/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c2 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((17353/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3753321/10000000) (δ := 16153/1000000000) (ψ := 197137/500000) 320 35
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t2 : ((7657965561/156250000000 : ℚ) : ℝ) ≤ stT320 2 := by
  have hc : ((1083/15625 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7657965561/156250000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((1083/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c3 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((23967/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -435457/2500000) (δ := 4001/250000000) (ψ := 197137/500000) 320 56
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t3 : ((553421920961/1250000000000 : ℚ) : ℝ) ≤ stT320 3 := by
  have hc : ((191711/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((553421920961/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((191711/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c4 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-483787/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7215597/10000000) (δ := 16011/1000000000) (ψ := 197137/500000) 320 71
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t4 : ((-2419185483837/5000000000000 : ℚ) : ℝ) ≤ stT320 4 := by
  have hc : ((-483837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2419185483837/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-483837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c5 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((413983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1488313/10000000) (δ := 16013/1000000000) (ψ := 197137/500000) 320 82
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t5 : ((370232851391/1000000000000 : ℚ) : ℝ) ≤ stT320 5 := by
  have hc : ((413933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((370232851391/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((413933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c6 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((72679/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1498609/5000000) (δ := 3231/200000000) (ψ := 197137/500000) 320 91
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t6 : ((148314529819/1000000000000 : ℚ) : ℝ) ≤ stT320 6 := by
  have hc : ((72659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148314529819/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((72659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c7 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((96597/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 654071/10000000) (δ := 16191/1000000000) (ψ := 197137/500000) 320 99
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t7 : ((91266118757/250000000000 : ℚ) : ℝ) ≤ stT320 7 := by
  have hc : ((96587/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91266118757/250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((96587/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c8 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((548171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2476551/10000000) (δ := 16163/1000000000) (ψ := 197137/500000) 320 106
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t8 : ((1937723106843/10000000000000 : ℚ) : ℝ) ≤ stT320 8 := by
  have hc : ((548071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1937723106843/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((548071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c9 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((540999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2497931/10000000) (δ := 8003/500000000) (ψ := 197137/500000) 320 112
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t9 : ((1802996486367/10000000000000 : ℚ) : ℝ) ≤ stT320 9 := by
  have hc : ((540899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1802996486367/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((540899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c10 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((267247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3250653/10000000) (δ := 8071/500000000) (ψ := 197137/500000) 320 117
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t10 : ((844792813719/10000000000000 : ℚ) : ℝ) ≤ stT320 10 := by
  have hc : ((267147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((844792813719/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((267147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c11 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((231831/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239749/2500000) (δ := 8063/500000000) (ψ := 197137/500000) 320 122
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t11 : ((349460642039/1250000000000 : ℚ) : ℝ) ≤ stT320 11 := by
  have hc : ((115903/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349460642039/1250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((115903/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c12 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-249723/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7736263/10000000) (δ := 16097/1000000000) (ψ := 197137/500000) 320 126
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t12 : ((-5632504207/19531250000 : ℚ) : ℝ) ≤ stT320 12 := by
  have hc : ((-62437/62500 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5632504207/19531250000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-62437/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c13 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-5671/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6769393/10000000) (δ := 8021/500000000) (ψ := 197137/500000) 320 131
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t13 : ((-125842060873/500000000000 : ℚ) : ℝ) ≤ stT320 13 := by
  have hc : ((-45373/50000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125842060873/500000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-45373/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c14 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-8647/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5393117/10000000) (δ := 16039/1000000000) (ψ := 197137/500000) 320 134
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t14 : ((-369828169101/2500000000000 : ℚ) : ℝ) ≤ stT320 14 := by
  have hc : ((-138377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369828169101/2500000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-138377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c15 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((311679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35069/156250) (δ := 16011/1000000000) (ψ := 197137/500000) 320 138
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t15 : ((201155584613/1250000000000 : ℚ) : ℝ) ≤ stT320 15 := by
  have hc : ((311629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201155584613/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((311629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c16 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((617687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1131247/5000000) (δ := 16089/1000000000) (ψ := 197137/500000) 320 141
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t16 : ((617587/4000000 : ℚ) : ℝ) ≤ stT320 16 := by
  have hc : ((617587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((617587/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((617587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c17 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((57613/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 909571/2500000) (δ := 2021/125000000) (ψ := 197137/500000) 320 144
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t17 : ((34902691857/1250000000000 : ℚ) : ℝ) ≤ stT320 17 := by
  have hc : ((57563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34902691857/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((57563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c18 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((62439/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448223/2000000) (δ := 16157/1000000000) (ψ := 197137/500000) 320 147
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t18 : ((73573263219/500000000000 : ℚ) : ℝ) ≤ stT320 18 := by
  have hc : ((62429/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73573263219/500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((62429/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c19 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((795111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325803/2000000) (δ := 8039/500000000) (ψ := 197137/500000) 320 150
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t19 : ((1823880050727/10000000000000 : ℚ) : ℝ) ≤ stT320 19 := by
  have hc : ((795011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1823880050727/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((795011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c20 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-998527/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1543653/2000000) (δ := 16003/1000000000) (ψ := 197137/500000) 320 153
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t20 : ((-558249469659/2500000000000 : ℚ) : ℝ) ≤ stT320 20 := by
  have hc : ((-998627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558249469659/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-998627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c21 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((999167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6377/625000) (δ := 16189/1000000000) (ψ := 197137/500000) 320 155
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t21 : ((1090071013963/5000000000000 : ℚ) : ℝ) ≤ stT320 21 := by
  have hc : ((999067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1090071013963/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((999067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c22 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-130127/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2849021/5000000) (δ := 16029/1000000000) (ψ := 197137/500000) 320 157
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t22 : ((-34684305647/250000000000 : ℚ) : ℝ) ≤ stT320 22 := by
  have hc : ((-130147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34684305647/250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-130147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c23 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-174923/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -733051/1250000) (δ := 16053/1000000000) (ψ := 197137/500000) 320 160
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t23 : ((-18239597373/125000000000 : ℚ) : ℝ) ≤ stT320 23 := by
  have hc : ((-43737/62500 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18239597373/125000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-43737/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c24 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((137089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1616327/5000000) (δ := 3233/200000000) (ψ := 197137/500000) 320 162
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t24 : ((279729625399/5000000000000 : ℚ) : ℝ) ≤ stT320 24 := by
  have hc : ((137039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279729625399/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((137039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c25 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((69929/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1990981/10000000) (δ := 2003/125000000) (ψ := 197137/500000) 320 164
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t25 : ((69919/500000 : ℚ) : ℝ) ≤ stT320 25 := by
  have hc : ((69919/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69919/500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((69919/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c26 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((171987/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2030347/10000000) (δ := 16193/1000000000) (ψ := 197137/500000) 320 166
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t26 : ((168622583941/1250000000000 : ℚ) : ℝ) ≤ stT320 26 := by
  have hc : ((85981/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168622583941/1250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((85981/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c27 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((33243/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1627017/5000000) (δ := 2001/125000000) (ψ := 197137/500000) 320 168
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t27 : ((255808389/5000000000 : ℚ) : ℝ) ≤ stT320 27 := by
  have hc : ((66461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255808389/5000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((66461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c28 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-612741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5575801/10000000) (δ := 16181/1000000000) (ψ := 197137/500000) 320 170
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t28 : ((-1158161017143/10000000000000 : ℚ) : ℝ) ≤ stT320 28 := by
  have hc : ((-612841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1158161017143/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-612841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c29 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-36427/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1697319/2500000) (δ := 8037/500000000) (ψ := 197137/500000) 320 171
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t29 : ((-33825345587/200000000000 : ℚ) : ℝ) ≤ stT320 29 := by
  have hc : ((-36431/40000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33825345587/200000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-36431/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c30 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((108427/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49891/200000) (δ := 1009/62500000) (ψ := 197137/500000) 320 173
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t30 : ((197923104587/2000000000000 : ℚ) : ℝ) ≤ stT320 30 := by
  have hc : ((108407/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197923104587/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((108407/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c31 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((118761/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2689457/10000000) (δ := 3209/200000000) (ψ := 197137/500000) 320 175
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t31 : ((13328509313/156250000000 : ℚ) : ℝ) ≤ stT320 31 := by
  have hc : ((7421/15625 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13328509313/156250000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((7421/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c32 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-942429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350077/500000) (δ := 3213/200000000) (ψ := 197137/500000) 320 176
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t32 : ((-1666171662743/10000000000000 : ℚ) : ℝ) ≤ stT320 32 := by
  have hc : ((-942529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1666171662743/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-942529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c33 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((996709/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202893/10000000) (δ := 4031/250000000) (ψ := 197137/500000) 320 178
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t33 : ((216859128573/1250000000000 : ℚ) : ℝ) ≤ stT320 33 := by
  have hc : ((996609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216859128573/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((996609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c34 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-122271/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7330633/10000000) (δ := 8047/500000000) (ψ := 197137/500000) 320 180
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t34 : ((-209714490531/1250000000000 : ℚ) : ℝ) ≤ stT320 34 := by
  have hc : ((-244567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209714490531/1250000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-244567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c35 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((998167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37851/2500000) (δ := 16201/1000000000) (ψ := 197137/500000) 320 181
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t35 : ((421760158659/2500000000000 : ℚ) : ℝ) ≤ stT320 35 := by
  have hc : ((998067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421760158659/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((998067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c36 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-469767/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21813/31250) (δ := 3219/200000000) (ψ := 197137/500000) 320 182
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t36 : ((-783028489939/5000000000000 : ℚ) : ℝ) ≤ stT320 36 := by
  have hc : ((-469817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-783028489939/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-469817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c37 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((106943/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1258283/5000000) (δ := 16123/1000000000) (ψ := 197137/500000) 320 184
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t37 : ((175780235847/2000000000000 : ℚ) : ℝ) ≤ stT320 37 := by
  have hc : ((106923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175780235847/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((106923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c38 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((320999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311003/1000000) (δ := 16173/1000000000) (ψ := 197137/500000) 320 185
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t38 : ((260283425193/5000000000000 : ℚ) : ℝ) ≤ stT320 38 := by
  have hc : ((320899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260283425193/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((320899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c39 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-49569/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -940687/1250000) (δ := 4011/250000000) (ψ := 197137/500000) 320 187
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t39 : ((-19845488467/125000000000 : ℚ) : ℝ) ≤ stT320 39 := by
  have hc : ((-24787/25000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19845488467/125000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-24787/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c40 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((370093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2979219/10000000) (δ := 16151/1000000000) (ψ := 197137/500000) 320 188
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t40 : ((292504996017/5000000000000 : ℚ) : ℝ) ≤ stT320 40 := by
  have hc : ((369993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292504996017/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((369993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c41 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((113789/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1066897/10000000) (δ := 3229/200000000) (ψ := 197137/500000) 320 189
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t41 : ((355377939561/2500000000000 : ℚ) : ℝ) ≤ stT320 41 := by
  have hc : ((227553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355377939561/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((227553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c42 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-280207/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2318507/5000000) (δ := 16037/1000000000) (ψ := 197137/500000) 320 190
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t42 : ((-216261615719/5000000000000 : ℚ) : ℝ) ≤ stT320 42 := by
  have hc : ((-280307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216261615719/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-280307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c43 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-124899/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7753451/10000000) (δ := 16073/1000000000) (ψ := 197137/500000) 320 191
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t43 : ((-190488288739/1250000000000 : ℚ) : ℝ) ≤ stT320 43 := by
  have hc : ((-249823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190488288739/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-249823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c44 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-512037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1317719/2500000) (δ := 4029/250000000) (ψ := 197137/500000) 320 193
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t44 : ((-772075719309/10000000000000 : ℚ) : ℝ) ≤ stT320 44 := by
  have hc : ((-512137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772075719309/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-512137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c45 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((181067/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3000599/10000000) (δ := 16009/1000000000) (ψ := 197137/500000) 320 194
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t45 : ((269844033087/5000000000000 : ℚ) : ℝ) ≤ stT320 45 := by
  have hc : ((181017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269844033087/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((181017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c46 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((90037/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -562721/5000000) (δ := 8051/500000000) (ψ := 197137/500000) 320 195
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t46 : ((132737519313/1000000000000 : ℚ) : ℝ) ≤ stT320 46 := by
  have hc : ((90027/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132737519313/1000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((90027/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c47 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((988971/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185817/5000000) (δ := 8097/500000000) (ψ := 197137/500000) 320 196
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t47 : ((1442415695279/10000000000000 : ℚ) : ℝ) ≤ stT320 47 := by
  have hc : ((988871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1442415695279/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((988871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c48 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((823889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1506391/10000000) (δ := 16087/1000000000) (ψ := 197137/500000) 320 197
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t48 : ((9512291583/80000000000 : ℚ) : ℝ) ≤ stT320 48 := by
  have hc : ((823789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9512291583/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((823789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c49 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((121559/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 573447/2500000) (δ := 16023/1000000000) (ψ := 197137/500000) 320 198
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t49 : ((173627090769/2000000000000 : ℚ) : ℝ) ≤ stT320 49 := by
  have hc : ((121539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173627090769/2000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((121539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c50 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((227143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549613/2000000) (δ := 1613/100000000) (ψ := 197137/500000) 320 199
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t50 : ((321157872809/5000000000000 : ℚ) : ℝ) ≤ stT320 50 := by
  have hc : ((227093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321157872809/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((227093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c51 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((50733/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2882181/10000000) (δ := 8083/500000000) (ψ := 197137/500000) 320 200
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t51 : ((3551145087/62500000000 : ℚ) : ℝ) ≤ stT320 51 := by
  have hc : ((101441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3551145087/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((101441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c52 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((468257/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1354349/5000000) (δ := 8029/500000000) (ψ := 197137/500000) 320 201
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t52 : ((2596866879/40000000000 : ℚ) : ℝ) ≤ stT320 52 := by
  have hc : ((468157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2596866879/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((468157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c53 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((312479/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 447859/2000000) (δ := 4013/250000000) (ψ := 197137/500000) 320 202
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t53 : ((85830807309/1000000000000 : ℚ) : ℝ) ≤ stT320 53 := by
  have hc : ((312429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85830807309/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((312429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c54 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((414353/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371253/2500000) (δ := 16159/1000000000) (ψ := 197137/500000) 320 203
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t54 : ((563794708581/5000000000000 : ℚ) : ℝ) ≤ stT320 54 := by
  have hc : ((414303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563794708581/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((414303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c55 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((983387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57041/1250000) (δ := 16137/1000000000) (ψ := 197137/500000) 320 204
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t55 : ((1325863207513/10000000000000 : ℚ) : ℝ) ≤ stT320 55 := by
  have hc : ((983287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1325863207513/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((983287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c56 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((472249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167367/2000000) (δ := 1603/100000000) (ψ := 197137/500000) 320 205
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t56 : ((315501178447/2500000000000 : ℚ) : ℝ) ≤ stT320 56 := by
  have hc : ((472199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315501178447/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((472199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c57 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((289193/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1192559/5000000) (δ := 201/12500000) (ψ := 197137/500000) 320 206
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t57 : ((95744789019/1250000000000 : ℚ) : ℝ) ≤ stT320 57 := by
  have hc : ((289143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95744789019/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((289143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c58 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-12611/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4179641/10000000) (δ := 4047/250000000) (ψ := 197137/500000) 320 207
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t58 : ((-6630190411/500000000000 : ℚ) : ℝ) ≤ stT320 58 := by
  have hc : ((-25247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6630190411/500000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-25247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c59 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-31679/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1242417/2000000) (δ := 4027/250000000) (ψ := 197137/500000) 320 208
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t59 : ((-4124778087/40000000000 : ℚ) : ℝ) ≤ stT320 59 := by
  have hc : ((-31683/40000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4124778087/40000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-31683/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c60 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-969367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1446719/2000000) (δ := 4027/250000000) (ψ := 197137/500000) 320 208
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t60 : ((-250315409933/2000000000000 : ℚ) : ℝ) ≤ stT320 60 := by
  have hc : ((-969467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250315409933/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-969467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c61 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-161469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296817/625000) (δ := 8001/500000000) (ψ := 197137/500000) 320 209
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t61 : ((-206803920511/5000000000000 : ℚ) : ℝ) ≤ stT320 61 := by
  have hc : ((-161519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206803920511/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-161519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c62 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((136473/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2049509/10000000) (δ := 16109/1000000000) (ψ := 197137/500000) 320 210
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t62 : ((173295446453/2000000000000 : ℚ) : ℝ) ≤ stT320 62 := by
  have hc : ((136453/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173295446453/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((136453/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c63 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((188333/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171627/2000000) (δ := 16187/1000000000) (ψ := 197137/500000) 320 211
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t63 : ((237251970753/2000000000000 : ℚ) : ℝ) ≤ stT320 63 := by
  have hc : ((188313/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237251970753/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((188313/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c64 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-8093/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1983729/5000000) (δ := 16079/1000000000) (ψ := 197137/500000) 320 212
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t64 : ((-10178758143/5000000000000 : ℚ) : ℝ) ≤ stT320 64 := by
  have hc : ((-8143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10178758143/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-8143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c65 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-121629/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7272061/10000000) (δ := 16031/1000000000) (ψ := 197137/500000) 320 213
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t65 : ((-75438895621/625000000000 : ℚ) : ℝ) ≤ stT320 65 := by
  have hc : ((-243283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75438895621/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-243283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c66 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-394919/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4941939/10000000) (δ := 16031/1000000000) (ψ := 197137/500000) 320 213
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t66 : ((-97246962477/2000000000000 : ℚ) : ℝ) ≤ stT320 66 := by
  have hc : ((-395019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97246962477/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-395019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c67 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((874827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158037/1250000) (δ := 8069/500000000) (ψ := 197137/500000) 320 214
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t67 : ((534324363769/5000000000000 : ℚ) : ℝ) ≤ stT320 67 := by
  have hc : ((874727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((534324363769/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((874727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c68 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((509119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -647897/2500000) (δ := 8079/500000000) (ψ := 197137/500000) 320 215
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t68 : ((308638071441/5000000000000 : ℚ) : ℝ) ≤ stT320 68 := by
  have hc : ((509019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308638071441/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((509019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c69 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-880733/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6620511/10000000) (δ := 16051/1000000000) (ψ := 197137/500000) 320 216
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t69 : ((-1060398734547/10000000000000 : ℚ) : ℝ) ≤ stT320 69 := by
  have hc : ((-880833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1060398734547/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-880833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c70 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-187957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4890449/10000000) (δ := 16051/1000000000) (ψ := 197137/500000) 320 216
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t70 : ((-224711418603/5000000000000 : ℚ) : ℝ) ≤ stT320 70 := by
  have hc : ((-188007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224711418603/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-188007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c71 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((488799/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265083/5000000) (δ := 16059/1000000000) (ψ := 197137/500000) 320 217
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t71 : ((580038026969/5000000000000 : ℚ) : ℝ) ≤ stT320 71 := by
  have hc : ((488749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((580038026969/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((488749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c72 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-386/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3988757/10000000) (δ := 16167/1000000000) (ψ := 197137/500000) 320 218
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t72 : ((-456747057/156250000000 : ℚ) : ℝ) ≤ stT320 72 := by
  have hc : ((-6201/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-456747057/156250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-6201/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c73 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-948211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7045883/10000000) (δ := 16167/1000000000) (ψ := 197137/500000) 320 218
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t73 : ((-277478643533/2500000000000 : ℚ) : ℝ) ≤ stT320 73 := by
  have hc : ((-948311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277478643533/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-948311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c74 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((31511/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2222399/10000000) (δ := 16129/1000000000) (ψ := 197137/500000) 320 219
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t74 : ((4578121107/62500000000 : ℚ) : ℝ) ≤ stT320 74 := by
  have hc : ((15753/25000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4578121107/62500000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((15753/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c75 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((90927/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686771/2500000) (δ := 8011/500000000) (ψ := 197137/500000) 320 220
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t75 : ((1049703129/20000000000 : ℚ) : ℝ) ≤ stT320 75 := by
  have hc : ((90907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1049703129/20000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((90907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c76 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-499999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1962269/2500000) (δ := 8011/500000000) (ψ := 197137/500000) 320 220
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t76 : ((-573595706871/5000000000000 : ℚ) : ℝ) ≤ stT320 76 := by
  have hc : ((-500049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573595706871/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-500049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c77 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((506637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2598793/10000000) (δ := 2011/125000000) (ψ := 197137/500000) 320 221
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t77 : ((115450419577/2000000000000 : ℚ) : ℝ) ≤ stT320 77 := by
  have hc : ((506537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115450419577/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((506537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c78 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((88111/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55729/200000) (δ := 3239/200000000) (ψ := 197137/500000) 320 222
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t78 : ((99743413207/2000000000000 : ℚ) : ℝ) ≤ stT320 78 := by
  have hc : ((88091/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99743413207/2000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((88091/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c79 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-983899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29619/40000) (δ := 3239/200000000) (ψ := 197137/500000) 320 222
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t79 : ((-34596420841/312500000000 : ℚ) : ℝ) ≤ stT320 79 := by
  have hc : ((-983999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34596420841/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-983999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c80 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((11911/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879913/5000000) (δ := 161/10000000) (ψ := 197137/500000) 320 223
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t80 : ((213042306183/2500000000000 : ℚ) : ℝ) ≤ stT320 80 := by
  have hc : ((190551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213042306183/2500000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((190551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c81 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-8313/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4010137/10000000) (δ := 1601/100000000) (ψ := 197137/500000) 320 224
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t81 : ((-579028241/156250000000 : ℚ) : ℝ) ≤ stT320 81 := by
  have hc : ((-4169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-579028241/156250000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-4169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c82 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-136559/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5805943/10000000) (δ := 1601/100000000) (ψ := 197137/500000) 320 224
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t82 : ((-37706593741/500000000000 : ℚ) : ℝ) ≤ stT320 82 := by
  have hc : ((-136579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37706593741/500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-136579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c83 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((996643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2049/100000) (δ := 16117/1000000000) (ψ := 197137/500000) 320 225
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t83 : ((546923725803/5000000000000 : ℚ) : ℝ) ≤ stT320 83 := by
  have hc : ((996543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546923725803/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((996543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c84 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-410163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -791493/1250000) (δ := 32179/1000000000) (ψ := 197137/500000) 320 226
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t84 : ((-44757930217/500000000000 : ℚ) : ℝ) ≤ stT320 84 := by
  have hc : ((-410213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44757930217/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-410213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c85 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((31129/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24497/78125) (δ := 16179/1000000000) (ψ := 197137/500000) 320 226
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t85 : ((8438321397/250000000000 : ℚ) : ℝ) ≤ stT320 85 := by
  have hc : ((31119/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8438321397/250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((31119/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c86 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((17547/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3215547/10000000) (δ := 2009/125000000) (ψ := 197137/500000) 320 227
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t86 : ((75658657301/2500000000000 : ℚ) : ℝ) ≤ stT320 86 := by
  have hc : ((70163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75658657301/2500000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((70163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c87 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-746291/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6033173/10000000) (δ := 2009/125000000) (ψ := 197137/500000) 320 227
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t87 : ((-800215494183/10000000000000 : ℚ) : ℝ) ≤ stT320 87 := by
  have hc : ((-746391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-800215494183/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-746391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c88 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((488729/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53183/1000000) (δ := 8019/500000000) (ψ := 197137/500000) 320 228
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t88 : ((520933280037/5000000000000 : ℚ) : ℝ) ≤ stT320 88 := by
  have hc : ((488679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520933280037/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((488679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c89 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-965999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7200193/10000000) (δ := 8073/500000000) (ψ := 197137/500000) 320 229
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t89 : ((-512031503901/5000000000000 : ℚ) : ℝ) ≤ stT320 89 := by
  have hc : ((-966099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512031503901/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-966099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c90 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((767811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1738447/10000000) (δ := 8073/500000000) (ψ := 197137/500000) 320 229
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t90 : ((202309505853/2500000000000 : ℚ) : ℝ) ≤ stT320 90 := by
  have hc : ((767711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202309505853/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((767711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c91 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-231359/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5129637/10000000) (δ := 643/20000000) (ψ := 197137/500000) 320 230
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t91 : ((-48516516713/1000000000000 : ℚ) : ℝ) ≤ stT320 91 := by
  have hc : ((-231409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48516516713/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-231409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c92 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((125027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3613603/10000000) (δ := 323/20000000) (ψ := 197137/500000) 320 230
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t92 : ((32561348061/2500000000000 : ℚ) : ℝ) ≤ stT320 92 := by
  have hc : ((124927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32561348061/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((124927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c93 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((191353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86141/250000) (δ := 16043/1000000000) (ψ := 197137/500000) 320 231
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t93 : ((198319989603/10000000000000 : ℚ) : ℝ) ≤ stT320 93 := by
  have hc : ((191253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198319989603/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((191253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c94 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-227977/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25553/50000) (δ := 16043/1000000000) (ψ := 197137/500000) 320 231
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t94 : ((-117596032197/2500000000000 : ℚ) : ℝ) ≤ stT320 94 := by
  have hc : ((-228027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117596032197/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-228027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c95 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((164493/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2131683/10000000) (δ := 16067/1000000000) (ψ := 197137/500000) 320 232
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t95 : ((21092568713/312500000000 : ℚ) : ℝ) ≤ stT320 95 := by
  have hc : ((41117/62500 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21092568713/312500000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((41117/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c96 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-800031/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6245357/10000000) (δ := 16067/1000000000) (ψ := 197137/500000) 320 232
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t96 : ((-816630501351/10000000000000 : ℚ) : ℝ) ≤ stT320 96 := by
  have hc : ((-800131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-816630501351/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-800131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c97 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((178409/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -586183/5000000) (δ := 8087/500000000) (ψ := 197137/500000) 320 233
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t97 : ((90563278797/1000000000000 : ℚ) : ℝ) ≤ stT320 97 := by
  have hc : ((178389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90563278797/1000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((178389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c98 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-946541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3516417/5000000) (δ := 8087/500000000) (ψ := 197137/500000) 320 233
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t98 : ((-956252246073/10000000000000 : ℚ) : ℝ) ≤ stT320 98 := by
  have hc : ((-946641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-956252246073/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-946641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c99 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((15244/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55321/1000000) (δ := 16121/1000000000) (ψ := 197137/500000) 320 234
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t99 : ((245107418523/2500000000000 : ℚ) : ℝ) ≤ stT320 99 := by
  have hc : ((243879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245107418523/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((243879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c100 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-989247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 748703/1000000) (δ := 16121/1000000000) (ψ := 197137/500000) 320 234
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t100 : ((-989347/10000000 : ℚ) : ℝ) ≤ stT320 100 := by
  have hc : ((-989347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-989347/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-989347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c101 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((994571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -260613/10000000) (δ := 8007/500000000) (ψ := 197137/500000) 320 235
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t101 : ((989535440427/10000000000000 : ℚ) : ℝ) ≤ stT320 101 := by
  have hc : ((994471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((989535440427/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((994471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c102 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-995669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7621227/10000000) (δ := 8007/500000000) (ψ := 197137/500000) 320 235
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t102 : ((-246489670953/2500000000000 : ℚ) : ℝ) ≤ stT320 102 := by
  have hc : ((-995769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246489670953/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-995769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c103 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((993651/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2202/78125) (δ := 503/31250000) (ψ := 197137/500000) 320 236
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t103 : ((978974613279/10000000000000 : ℚ) : ℝ) ≤ stT320 103 := by
  have hc : ((993551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((978974613279/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((993551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c104 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-493411/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465479/625000) (δ := 503/31250000) (ψ := 197137/500000) 320 236
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t104 : ((-483878480841/5000000000000 : ℚ) : ℝ) ≤ stT320 104 := by
  have hc : ((-493461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483878480841/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-493461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c105 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((970889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6047/100000) (δ := 81/5000000) (ψ := 197137/500000) 320 237
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t105 : ((9473929851/100000000000 : ℚ) : ℝ) ≤ stT320 105 := by
  have hc : ((970789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9473929851/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((970789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c106 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-469637/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348913/500000) (δ := 81/5000000) (ψ := 197137/500000) 320 237
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t106 : ((-228100203741/2500000000000 : ℚ) : ℝ) ≤ stT320 106 := by
  have hc : ((-469687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228100203741/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-469687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c107 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((883673/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1217863/10000000) (δ := 16093/1000000000) (ψ := 197137/500000) 320 238
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t107 : ((53386364233/625000000000 : ℚ) : ℝ) ≤ stT320 107 := by
  have hc : ((883573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53386364233/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((883573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c108 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-79489/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6224057/10000000) (δ := 16093/1000000000) (ψ := 197137/500000) 320 238
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t108 : ((-76497992249/1000000000000 : ℚ) : ℝ) ≤ stT320 108 := by
  have hc : ((-79499/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76497992249/1000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-79499/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c109 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((166073/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1055313/5000000) (δ := 16017/1000000000) (ψ := 197137/500000) 320 239
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t109 : ((2485079557/39062500000 : ℚ) : ℝ) ≤ stT320 109 := by
  have hc : ((10378/15625 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2485079557/39062500000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((10378/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c110 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-242933/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2597687/5000000) (δ := 16017/1000000000) (ψ := 197137/500000) 320 239
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t110 : ((-231675300129/5000000000000 : ℚ) : ℝ) ≤ stT320 110 := by
  have hc : ((-242983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231675300129/5000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-242983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c111 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((258751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3272669/10000000) (δ := 129/8000000) (ψ := 197137/500000) 320 240
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t111 : ((245500407207/10000000000000 : ℚ) : ℝ) ≤ stT320 111 := by
  have hc : ((258651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245500407207/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((258651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c112 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((1239/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3902211/10000000) (δ := 129/8000000) (ψ := 197137/500000) 320 240
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t112 : ((2317866683/2500000000000 : ℚ) : ℝ) ≤ stT320 112 := by
  have hc : ((2453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2317866683/2500000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((2453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c113 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-18889/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4694553/10000000) (δ := 16171/1000000000) (ψ := 197137/500000) 320 241
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t113 : ((-71100633901/2500000000000 : ℚ) : ℝ) ≤ stT320 113 := by
  have hc : ((-75581/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71100633901/2500000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-75581/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c114 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((588519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2353927/10000000) (δ := 16171/1000000000) (ψ := 197137/500000) 320 241
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t114 : ((110220881823/2000000000000 : ℚ) : ℝ) ≤ stT320 114 := by
  have hc : ((588419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110220881823/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((588419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c115 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-414141/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1591769/2500000) (δ := 251/15625000) (ψ := 197137/500000) 320 242
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t115 : ((-77247035691/1000000000000 : ℚ) : ℝ) ≤ stT320 115 := by
  have hc : ((-414191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77247035691/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-414191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c116 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((975077/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139831/2500000) (δ := 251/15625000) (ψ := 197137/500000) 320 242
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t116 : ((226310686263/2500000000000 : ℚ) : ℝ) ≤ stT320 116 := by
  have hc : ((974977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226310686263/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((974977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c117 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-985407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1856591/2500000) (δ := 251/15625000) (ψ := 197137/500000) 320 242
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t117 : ((-911102207007/10000000000000 : ℚ) : ℝ) ≤ stT320 117 := by
  have hc : ((-985507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-911102207007/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-985507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c118 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((831377/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1473039/10000000) (δ := 8023/500000000) (ψ := 197137/500000) 320 243
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t118 : ((382625996499/5000000000000 : ℚ) : ℝ) ≤ stT320 118 := by
  have hc : ((831277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((382625996499/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((831277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c119 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-514483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5278001/10000000) (δ := 8023/500000000) (ψ := 197137/500000) 320 243
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t119 : ((-471717721517/10000000000000 : ℚ) : ℝ) ≤ stT320 119 := by
  have hc : ((-514583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-471717721517/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-514583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c120 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((4787/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1867661/5000000) (δ := 16153/1000000000) (ψ := 197137/500000) 320 244
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t120 : ((1745681301/250000000000 : ℚ) : ℝ) ≤ stT320 120 := by
  have hc : ((19123/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1745681301/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((19123/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c121 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((49747/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1451859/5000000) (δ := 16153/1000000000) (ψ := 197137/500000) 320 244
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t121 : ((9042627321/250000000000 : ℚ) : ℝ) ≤ stT320 121 := by
  have hc : ((99469/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9042627321/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((99469/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c122 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-793867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3109923/5000000) (δ := 16143/1000000000) (ψ := 197137/500000) 320 245
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t122 : ((-359412187593/5000000000000 : ℚ) : ℝ) ≤ stT320 122 := by
  have hc : ((-793967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-359412187593/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-793967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c123 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((992283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155397/5000000) (δ := 16143/1000000000) (ψ := 197137/500000) 320 245
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t123 : ((894620653427/10000000000000 : ℚ) : ℝ) ≤ stT320 123 := by
  have hc : ((992183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((894620653427/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((992183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c124 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-182111/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3394277/5000000) (δ := 16143/1000000000) (ψ := 197137/500000) 320 245
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t124 : ((-163558555537/2000000000000 : ℚ) : ℝ) ≤ stT320 124 := by
  have hc : ((-182131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163558555537/2000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-182131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c125 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((271219/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2493649/10000000) (δ := 3207/200000000) (ψ := 197137/500000) 320 246
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t125 : ((242540875163/5000000000000 : ℚ) : ℝ) ≤ stT320 125 := by
  have hc : ((271169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242540875163/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((271169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c126 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((18431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3880911/10000000) (δ := 3207/200000000) (ψ := 197137/500000) 320 246
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t126 : ((1633053797/1000000000000 : ℚ) : ℝ) ≤ stT320 126 := by
  have hc : ((18331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1633053797/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((18331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c127 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-294731/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1375743/2500000) (δ := 643/40000000) (ψ := 197137/500000) 320 247
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t127 : ((-261575983817/5000000000000 : ℚ) : ℝ) ≤ stT320 127 := by
  have hc : ((-294781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261575983817/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-294781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c128 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((952749/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192897/2500000) (δ := 643/40000000) (ψ := 197137/500000) 320 247
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t128 : ((842030256067/10000000000000 : ℚ) : ℝ) ≤ stT320 128 := by
  have hc : ((952649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((842030256067/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((952649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c129 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-470933/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1749337/2500000) (δ := 643/40000000) (ψ := 197137/500000) 320 247
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t129 : ((-414677453333/5000000000000 : ℚ) : ℝ) ≤ stT320 129 := by
  have hc : ((-470983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-414677453333/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-470983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c130 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((529143/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -506603/2000000) (δ := 8091/500000000) (ψ := 197137/500000) 320 248
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t130 : ((232000697747/5000000000000 : ℚ) : ℝ) ≤ stT320 130 := by
  have hc : ((529043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232000697747/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((529043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c131 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((32873/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 719461/2000000) (δ := 8091/500000000) (ψ := 197137/500000) 320 248
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t131 : ((224214289/19531250000 : ℚ) : ℝ) ≤ stT320 131 := by
  have hc : ((2053/15625 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224214289/19531250000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((2053/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c132 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-2327/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6026979/10000000) (δ := 8057/500000000) (ψ := 197137/500000) 320 249
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t132 : ((-32410675193/500000000000 : ℚ) : ℝ) ≤ stT320 132 := by
  have hc : ((-37237/50000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32410675193/500000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-37237/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c133 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((999991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10781/10000000) (δ := 8057/500000000) (ψ := 197137/500000) 320 249
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t133 : ((867014485119/10000000000000 : ℚ) : ℝ) ≤ stT320 133 := by
  have hc : ((999891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((867014485119/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((999891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c134 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-147657/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6003301/10000000) (δ := 16057/500000000) (ψ := 197137/500000) 320 249
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t134 : ((-127573582313/2000000000000 : ℚ) : ℝ) ≤ stT320 134 := by
  have hc : ((-147677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127573582313/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-147677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c135 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((68063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1878351/5000000) (δ := 16007/1000000000) (ψ := 197137/500000) 320 250
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t135 : ((29246585753/5000000000000 : ℚ) : ℝ) ≤ stT320 135 := by
  have hc : ((67963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29246585753/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((67963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c136 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((40827/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1073689/5000000) (δ := 16007/1000000000) (ψ := 197137/500000) 320 250
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t136 : ((35003466559/625000000000 : ℚ) : ℝ) ≤ stT320 136 := by
  have hc : ((163283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35003466559/625000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((163283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c137 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-998097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1539941/2000000) (δ := 2013/125000000) (ψ := 197137/500000) 320 251
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t137 : ((-426408796263/5000000000000 : ℚ) : ℝ) ≤ stT320 137 := by
  have hc : ((-998197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426408796263/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-998197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c138 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((364951/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -376309/2000000) (δ := 2013/125000000) (ψ := 197137/500000) 320 251
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t138 : ((38828020707/625000000000 : ℚ) : ℝ) ≤ stT320 138 := by
  have hc : ((364901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38828020707/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((364901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c139 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((6459/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778939/2000000) (δ := 2013/125000000) (ψ := 197137/500000) 320 251
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t139 : ((1359009223/1250000000000 : ℚ) : ℝ) ≤ stT320 139 := by
  have hc : ((6409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1359009223/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((6409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c140 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-189557/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6078469/10000000) (δ := 253/15625000) (ψ := 197137/500000) 320 252
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t140 : ((-16022617521/250000000000 : ℚ) : ℝ) ≤ stT320 140 := by
  have hc : ((-94791/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16022617521/250000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-94791/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c141 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((988193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -384549/10000000) (δ := 253/15625000) (ψ := 197137/500000) 320 252
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t141 : ((832123508043/10000000000000 : ℚ) : ℝ) ≤ stT320 141 := by
  have hc : ((988093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((832123508043/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((988093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c142 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-63933/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5269211/10000000) (δ := 253/15625000) (ψ := 197137/500000) 320 252
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t142 : ((-53661912581/1250000000000 : ℚ) : ℝ) ≤ stT320 142 := by
  have hc : ((-127891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53661912581/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-127891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c143 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-175703/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150771/312500) (δ := 3217/200000000) (ψ := 197137/500000) 320 253
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t143 : ((-146972215979/5000000000000 : ℚ) : ℝ) ≤ stT320 143 := by
  have hc : ((-175753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146972215979/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-175753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c144 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((59707/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5861/78125) (δ := 3217/200000000) (ψ := 197137/500000) 320 253
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t144 : ((199002420399/2500000000000 : ℚ) : ℝ) ≤ stT320 144 := by
  have hc : ((238803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199002420399/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((238803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c145 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-809821/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 392913/625000) (δ := 3217/200000000) (ψ := 197137/500000) 320 253
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t145 : ((-134520588811/2000000000000 : ℚ) : ℝ) ≤ stT320 145 := by
  have hc : ((-809921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134520588811/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-809921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c146 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((791/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -784607/2000000) (δ := 641/40000000) (ψ := 197137/500000) 320 254
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t146 : ((122651061/1000000000000 : ℚ) : ℝ) ≤ stT320 146 := by
  have hc : ((741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122651061/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c147 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((816731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 307537/2000000) (δ := 641/40000000) (ψ := 197137/500000) 320 254
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t147 : ((336772907983/5000000000000 : ℚ) : ℝ) ≤ stT320 147 := by
  have hc : ((816631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336772907983/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((816631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c148 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-58559/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1392289/2000000) (δ := 641/40000000) (ψ := 197137/500000) 320 254
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t148 : ((-38512274139/500000000000 : ℚ) : ℝ) ≤ stT320 148 := by
  have hc : ((-234261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38512274139/500000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-234261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c149 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((112577/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1679619/5000000) (δ := 4033/250000000) (ψ := 197137/500000) 320 255
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t149 : ((92185606737/5000000000000 : ℚ) : ℝ) ≤ stT320 149 := by
  have hc : ((112527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92185606737/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((112527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c150 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((87379/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 995941/5000000) (δ := 4033/250000000) (ψ := 197137/500000) 320 255
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t150 : ((8916799723/156250000000 : ℚ) : ℝ) ≤ stT320 150 := by
  have hc : ((174733/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8916799723/156250000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((174733/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c151 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-976209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3653781/5000000) (δ := 4033/250000000) (ψ := 197137/500000) 320 255
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t151 : ((-794509524801/10000000000000 : ℚ) : ℝ) ≤ stT320 151 := by
  have hc : ((-976309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-794509524801/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-976309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c152 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((1983/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1559921/5000000) (δ := 4041/250000000) (ψ := 197137/500000) 320 256
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t152 : ((12863345913/500000000000 : ℚ) : ℝ) ≤ stT320 152 := by
  have hc : ((15859/50000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12863345913/500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((15859/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c153 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((659659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1063039/5000000) (δ := 4041/250000000) (ψ := 197137/500000) 320 256
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t153 : ((133305448167/2500000000000 : ℚ) : ℝ) ≤ stT320 153 := by
  have hc : ((659559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133305448167/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((659559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c154 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-978763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3668919/5000000) (δ := 4041/250000000) (ψ := 197137/500000) 320 256
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t154 : ((-788790319249/10000000000000 : ℚ) : ℝ) ≤ stT320 154 := by
  have hc : ((-978863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-788790319249/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-978863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c155 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((72433/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25537/80000) (δ := 2007/125000000) (ψ := 197137/500000) 320 257
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t155 : ((7269935169/312500000000 : ℚ) : ℝ) ≤ stT320 155 := by
  have hc : ((9051/31250 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7269935169/312500000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((9051/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c156 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((710183/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 390519/2000000) (δ := 2007/125000000) (ψ := 197137/500000) 320 257
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t156 : ((888313833/15625000000 : ℚ) : ℝ) ≤ stT320 156 := by
  have hc : ((710083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((888313833/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((710083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c157 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-475271/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1412887/2000000) (δ := 2007/125000000) (ψ := 197137/500000) 320 257
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t157 : ((-379347510927/5000000000000 : ℚ) : ℝ) ≤ stT320 157 := by
  have hc : ((-475321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379347510927/5000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-475321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c158 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((7231/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -445521/1250000) (δ := 8027/500000000) (ψ := 197137/500000) 320 258
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t158 : ((2874347441/250000000000 : ℚ) : ℝ) ≤ stT320 158 := by
  have hc : ((3613/25000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2874347441/250000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((3613/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c159 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((829113/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185399/1250000) (δ := 8027/500000000) (ψ := 197137/500000) 320 258
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t159 : ((657449588663/10000000000000 : ℚ) : ℝ) ≤ stT320 159 := by
  have hc : ((829013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((657449588663/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((829013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c160 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-53541/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 812359/1250000) (δ := 8027/500000000) (ψ := 197137/500000) 320 258
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t160 : ((-16933139773/250000000000 : ℚ) : ℝ) ≤ stT320 160 := by
  have hc : ((-214189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16933139773/250000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-214189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c161 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-118799/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4224691/10000000) (δ := 16161/1000000000) (ψ := 197137/500000) 320 259
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t161 : ((-93705609789/10000000000000 : ℚ) : ℝ) ≤ stT320 161 := by
  have hc : ((-118899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93705609789/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-118899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c162 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((239449/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 728909/10000000) (δ := 16161/1000000000) (ψ := 197137/500000) 320 259
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t162 : ((1469603217/19531250000 : ℚ) : ℝ) ≤ stT320 162 := by
  have hc : ((14964/15625 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1469603217/19531250000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((14964/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c163 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-636549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5652029/10000000) (δ := 16161/1000000000) (ψ := 197137/500000) 320 259
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t163 : ((-498662332389/10000000000000 : ℚ) : ℝ) ≤ stT320 163 := by
  have hc : ((-636649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498662332389/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-636649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c164 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-237249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206519/400000) (δ := 3227/200000000) (ψ := 197137/500000) 320 260
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t164 : ((-185299432831/5000000000000 : ℚ) : ℝ) ≤ stT320 164 := by
  have hc : ((-237299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185299432831/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-237299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c165 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((992819/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11991/400000) (δ := 3227/200000000) (ψ := 197137/500000) 320 260
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t165 : ((386414878031/5000000000000 : ℚ) : ℝ) ≤ stT320 165 := by
  have hc : ((992719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386414878031/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((992719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c166 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-4809/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 906813/2000000) (δ := 3227/200000000) (ψ := 197137/500000) 320 260
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t166 : ((-3734062461/200000000000 : ℚ) : ℝ) ≤ stT320 166 := by
  have hc : ((-4811/20000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3734062461/200000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-4811/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c167 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-828717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3184509/5000000) (δ := 4007/250000000) (ψ := 197137/500000) 320 261
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t167 : ((-10021226347/156250000000 : ℚ) : ℝ) ≤ stT320 167 := by
  have hc : ((-828817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10021226347/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-828817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c168 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((40189/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -796469/5000000) (δ := 4007/250000000) (ψ := 197137/500000) 320 261
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t168 : ((968831217/15625000000 : ℚ) : ℝ) ≤ stT320 168 := by
  have hc : ((5023/6250 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((968831217/15625000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((5023/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c169 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((303949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1577451/5000000) (δ := 4007/250000000) (ψ := 197137/500000) 320 261
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t169 : ((23372976627/1000000000000 : ℚ) : ℝ) ≤ stT320 169 := by
  have hc : ((303849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23372976627/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((303849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c170 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-499983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7833301/10000000) (δ := 16083/1000000000) (ψ := 197137/500000) 320 262
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t170 : ((-76701561969/1000000000000 : ℚ) : ℝ) ≤ stT320 170 := by
  have hc : ((-500033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76701561969/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-500033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c171 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((154579/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3141221/10000000) (δ := 16083/1000000000) (ψ := 197137/500000) 320 262
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t171 : ((118171262351/5000000000000 : ℚ) : ℝ) ≤ stT320 171 := by
  have hc : ((154529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118171262351/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((154529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c172 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((102499/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1523499/10000000) (δ := 16083/1000000000) (ψ := 197137/500000) 320 262
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t172 : ((39072568179/625000000000 : ℚ) : ℝ) ≤ stT320 172 := by
  have hc : ((204973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39072568179/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((204973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c173 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-38969/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6161179/10000000) (δ := 16083/1000000000) (ψ := 197137/500000) 320 262
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t173 : ((-7407846641/125000000000 : ℚ) : ℝ) ≤ stT320 173 := by
  have hc : ((-19487/25000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7407846641/125000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-19487/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c174 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-39267/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -308489/625000) (δ := 1619/100000000) (ψ := 197137/500000) 320 263
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t174 : ((-29775854423/1000000000000 : ℚ) : ℝ) ≤ stT320 174 := by
  have hc : ((-39277/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29775854423/1000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-39277/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c175 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((198029/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10977/312500) (δ := 1619/100000000) (ψ := 197137/500000) 320 263
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t175 : ((18710068419/250000000000 : ℚ) : ℝ) ≤ stT320 175 := by
  have hc : ((198009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18710068419/250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((198009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c176 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-6989/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131473/312500) (δ := 1619/100000000) (ψ := 197137/500000) 320 263
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t176 : ((-21091490199/2500000000000 : ℚ) : ℝ) ≤ stT320 176 := by
  have hc : ((-27981/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21091490199/2500000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-27981/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c177 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-234471/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1742047/2500000) (δ := 8053/500000000) (ψ := 197137/500000) 320 264
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t177 : ((-172127163/2441406250 : ℚ) : ℝ) ≤ stT320 177 := by
  have hc : ((-14656/15625 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172127163/2441406250 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-14656/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c178 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((276657/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -615287/2500000) (δ := 8053/500000000) (ψ := 197137/500000) 320 264
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t178 : ((207325521317/5000000000000 : ℚ) : ℝ) ≤ stT320 178 := by
  have hc : ((276607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207325521317/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((276607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c179 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((345373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 505173/2500000) (δ := 8053/500000000) (ψ := 197137/500000) 320 264
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t179 : ((51621299301/1000000000000 : ℚ) : ℝ) ≤ stT320 179 := by
  have hc : ((345323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51621299301/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((345323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c180 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-852213/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619373/2500000) (δ := 8053/500000000) (ψ := 197137/500000) 320 264
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t180 : ((-158819152107/2500000000000 : ℚ) : ℝ) ≤ stT320 180 := by
  have hc : ((-852313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158819152107/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-852313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c181 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-68303/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4798311/10000000) (δ := 4001/250000000) (ψ := 197137/500000) 320 265
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t181 : ((-10156828857/400000000000 : ℚ) : ℝ) ≤ stT320 181 := by
  have hc : ((-68323/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10156828857/400000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-68323/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c182 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((987817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -390631/10000000) (δ := 4001/250000000) (ψ := 197137/500000) 320 265
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t182 : ((732144238533/10000000000000 : ℚ) : ℝ) ≤ stT320 182 := by
  have hc : ((987717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((732144238533/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((987717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c183 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-6597/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3992969/10000000) (δ := 4001/250000000) (ψ := 197137/500000) 320 265
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t183 : ((-1223782021/625000000000 : ℚ) : ℝ) ≤ stT320 183 := by
  have hc : ((-3311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1223782021/625000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-3311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c184 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-245043/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3677657/5000000) (δ := 16111/1000000000) (ψ := 197137/500000) 320 266
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t184 : ((-4516664507/62500000000 : ℚ) : ℝ) ≤ stT320 184 := by
  have hc : ((-61267/62500 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4516664507/62500000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-61267/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c185 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((44397/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509617/5000000) (δ := 16111/1000000000) (ψ := 197137/500000) 320 266
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t185 : ((32632105783/1250000000000 : ℚ) : ℝ) ≤ stT320 185 := by
  have hc : ((88769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32632105783/1250000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((88769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c186 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((869127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646703/5000000) (δ := 16111/1000000000) (ψ := 197137/500000) 320 266
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t186 : ((127440202469/2000000000000 : ℚ) : ℝ) ≤ stT320 186 := by
  have hc : ((869027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127440202469/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((869027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c187 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-76877/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2791503/5000000) (δ := 16111/1000000000) (ψ := 197137/500000) 320 266
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t187 : ((-112454430667/2500000000000 : ℚ) : ℝ) ≤ stT320 187 := by
  have hc : ((-153779/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112454430667/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-153779/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c188 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-13959/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2929159/5000000) (δ := 3237/200000000) (ψ := 197137/500000) 320 267
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t188 : ((-407284253/8000000000 : ℚ) : ℝ) ≤ stT320 188 := by
  have hc : ((-13961/20000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-407284253/8000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-13961/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c189 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((399341/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -807119/5000000) (δ := 3237/200000000) (ψ := 197137/500000) 320 267
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t189 : ((9076283721/156250000000 : ℚ) : ℝ) ≤ stT320 189 := by
  have hc : ((399291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9076283721/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((399291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c190 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((251839/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303681/5000000) (δ := 3237/200000000) (ψ := 197137/500000) 320 267
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t190 : ((45666719141/1250000000000 : ℚ) : ℝ) ≤ stT320 190 := by
  have hc : ((251789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45666719141/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((251789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c191 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-913561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3403441/5000000) (δ := 3237/200000000) (ψ := 197137/500000) 320 267
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t191 : ((-26444090323/400000000000 : ℚ) : ℝ) ≤ stT320 191 := by
  have hc : ((-913661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26444090323/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-913661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c192 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-19579/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4723561/10000000) (δ := 16077/1000000000) (ψ := 197137/500000) 320 268
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t192 : ((-7067219951/312500000000 : ℚ) : ℝ) ≤ stT320 192 := by
  have hc : ((-78341/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7067219951/312500000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-78341/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c193 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((487163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -567721/10000000) (δ := 16077/1000000000) (ψ := 197137/500000) 320 268
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t193 : ((70126248819/1000000000000 : ℚ) : ℝ) ≤ stT320 193 := by
  have hc : ((487113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70126248819/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((487113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c194 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((71813/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3566679/10000000) (δ := 16077/1000000000) (ψ := 197137/500000) 320 268
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t194 : ((25761409977/2500000000000 : ℚ) : ℝ) ≤ stT320 194 := by
  have hc : ((71763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25761409977/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((71763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c195 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-498787/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7679799/10000000) (δ := 16077/1000000000) (ψ := 197137/500000) 320 268
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t195 : ((-71444931651/1000000000000 : ℚ) : ℝ) ≤ stT320 195 := by
  have hc : ((-498837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71444931651/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-498837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c196 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-3637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -984021/2500000) (δ := 16033/1000000000) (ψ := 197137/500000) 320 269
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t196 : ((-1334643391/5000000000000 : ℚ) : ℝ) ≤ stT320 196 := by
  have hc : ((-3737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1334643391/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-3737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c197 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((499269/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33799/2500000) (δ := 16033/1000000000) (ψ := 197137/500000) 320 269
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t197 : ((35567856093/500000000000 : ℚ) : ℝ) ≤ stT320 197 := by
  have hc : ((499219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35567856093/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((499219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c198 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-103353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1046459/2500000) (δ := 16033/1000000000) (ψ := 197137/500000) 320 269
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t198 : ((-7352094351/1000000000000 : ℚ) : ℝ) ≤ stT320 198 := by
  have hc : ((-103453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7352094351/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-103453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c199 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-989529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7491887/10000000) (δ := 807/50000000) (ψ := 197137/500000) 320 270
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t199 : ((-350765092389/5000000000000 : ℚ) : ℝ) ≤ stT320 199 := by
  have hc : ((-989629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350765092389/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-989629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c200 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((88551/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3481887/10000000) (δ := 807/50000000) (ψ := 197137/500000) 320 270
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t200 : ((31289794053/2500000000000 : ℚ) : ℝ) ≤ stT320 200 := by
  have hc : ((88501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31289794053/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((88501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c201 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((97941/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508193/10000000) (δ := 807/50000000) (ψ := 197137/500000) 320 270
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t201 : ((13815028239/200000000000 : ℚ) : ℝ) ≤ stT320 201 := by
  have hc : ((97931/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13815028239/200000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((97931/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c202 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-218761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4478353/10000000) (δ := 807/50000000) (ψ := 197137/500000) 320 270
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t202 : ((-76995080939/5000000000000 : ℚ) : ℝ) ≤ stT320 202 := by
  have hc : ((-218861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76995080939/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-218861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c203 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-194733/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7278971/10000000) (δ := 4039/250000000) (ψ := 197137/500000) 320 271
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t203 : ((-136689924839/2000000000000 : ℚ) : ℝ) ≤ stT320 203 := by
  have hc : ((-194753/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136689924839/2000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-194753/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c204 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((229621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3347771/10000000) (δ := 4039/250000000) (ψ := 197137/500000) 320 271
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t204 : ((8034841647/500000000000 : ℚ) : ℝ) ≤ stT320 204 := by
  have hc : ((229521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8034841647/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((229521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c205 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((12183/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 564229/10000000) (δ := 4039/250000000) (ψ := 197137/500000) 320 271
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t205 : ((3403239861/50000000000 : ℚ) : ℝ) ≤ stT320 205 := by
  have hc : ((48727/50000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3403239861/50000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((48727/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c206 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-210493/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4457189/10000000) (δ := 4039/250000000) (ψ := 197137/500000) 320 271
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t206 : ((-73363651631/5000000000000 : ℚ) : ℝ) ≤ stT320 206 := by
  have hc : ((-210593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73363651631/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-210593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c207 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-981831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3688347/5000000) (δ := 16049/1000000000) (ψ := 197137/500000) 320 272
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t207 : ((-682490159619/10000000000000 : ℚ) : ℝ) ≤ stT320 207 := by
  have hc : ((-981931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682490159619/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-981931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c208 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((161583/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760627/5000000) (δ := 16049/1000000000) (ψ := 197137/500000) 320 272
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t208 : ((895746201/80000000000 : ℚ) : ℝ) ≤ stT320 208 := by
  have hc : ((161483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((895746201/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((161483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c209 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((992037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157853/5000000) (δ := 16049/1000000000) (ψ := 197137/500000) 320 272
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t209 : ((343068355009/5000000000000 : ℚ) : ℝ) ≤ stT320 209 := by
  have hc : ((991937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((343068355009/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((991937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c210 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-82847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2067173/5000000) (δ := 16049/1000000000) (ψ := 197137/500000) 320 272
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t210 : ((-28619452251/5000000000000 : ℚ) : ℝ) ≤ stT320 210 := by
  have hc : ((-82947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28619452251/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-82947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c211 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-999477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7773137/10000000) (δ := 8031/500000000) (ψ := 197137/500000) 320 273
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t211 : ((-688137794533/10000000000000 : ℚ) : ℝ) ≤ stT320 211 := by
  have hc : ((-999577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-688137794533/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-999577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c212 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-3183/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3990657/10000000) (δ := 8031/500000000) (ψ := 197137/500000) 320 273
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t212 : ((-4389357973/2500000000000 : ℚ) : ℝ) ≤ stT320 212 := by
  have hc : ((-6391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4389357973/2500000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-6391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c213 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((995919/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225937/10000000) (δ := 8031/500000000) (ψ := 197137/500000) 320 273
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t213 : ((170580807243/2500000000000 : ℚ) : ℝ) ≤ stT320 213 := by
  have hc : ((995819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170580807243/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((995819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c214 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((161611/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3521183/10000000) (δ := 8031/500000000) (ψ := 197137/500000) 320 273
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t214 : ((22081299387/2000000000000 : ℚ) : ℝ) ≤ stT320 214 := by
  have hc : ((161511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22081299387/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((161511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c215 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-971033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7250783/10000000) (δ := 8031/500000000) (ψ := 197137/500000) 320 273
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t215 : ((-132461570067/2000000000000 : ℚ) : ℝ) ≤ stT320 215 := by
  have hc : ((-971133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132461570067/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-971133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c216 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-321343/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237243/500000) (δ := 16169/1000000000) (ψ := 197137/500000) 320 274
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t216 : ((-109357158701/5000000000000 : ℚ) : ℝ) ≤ stT320 216 := by
  have hc : ((-321443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109357158701/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-321443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c217 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((913131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52487/500000) (δ := 16169/1000000000) (ψ := 197137/500000) 320 274
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t217 : ((154951404041/2500000000000 : ℚ) : ℝ) ≤ stT320 217 := by
  have hc : ((913031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154951404041/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((913031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c218 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((7756/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131421/500000) (δ := 16169/1000000000) (ψ := 197137/500000) 320 274
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t218 : ((16806285447/500000000000 : ℚ) : ℝ) ≤ stT320 218 := by
  have hc : ((124071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16806285447/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((124071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c219 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-162113/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 314489/500000) (δ := 16169/1000000000) (ψ := 197137/500000) 320 274
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t219 : ((-54779714577/1000000000000 : ℚ) : ℝ) ≤ stT320 219 := by
  have hc : ((-162133/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54779714577/1000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-162133/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c220 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-673269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -721693/1250000) (δ := 16127/1000000000) (ψ := 197137/500000) 320 275
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t220 : ((-2269926899/50000000000 : ℚ) : ℝ) ≤ stT320 220 := by
  have hc : ((-673369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2269926899/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-673369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c221 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((163459/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268173/1250000) (δ := 16127/1000000000) (ψ := 197137/500000) 320 275
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t221 : ((1717773057/39062500000 : ℚ) : ℝ) ≤ stT320 221 := by
  have hc : ((81717/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1717773057/39062500000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((81717/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c222 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((832873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183287/1250000) (δ := 16127/1000000000) (ψ := 197137/500000) 320 275
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t222 : ((139730148897/2500000000000 : ℚ) : ℝ) ≤ stT320 222 := by
  have hc : ((832773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139730148897/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((832773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c223 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-438501/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 632727/1250000) (δ := 16127/1000000000) (ψ := 197137/500000) 320 275
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t223 : ((-5874183193/200000000000 : ℚ) : ℝ) ≤ stT320 223 := by
  have hc : ((-438601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5874183193/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-438601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c224 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-118853/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7066707/10000000) (δ := 801/50000000) (ψ := 197137/500000) 320 276
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t224 : ((-79420459287/1250000000000 : ℚ) : ℝ) ≤ stT320 224 := by
  have hc : ((-237731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79420459287/1250000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-237731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c225 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((168711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3503187/10000000) (δ := 801/50000000) (ψ := 197137/500000) 320 276
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t225 : ((56203610463/5000000000000 : ℚ) : ℝ) ≤ stT320 225 := by
  have hc : ((168611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56203610463/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((168611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c226 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((499921/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44453/10000000) (δ := 1601/50000000) (ψ := 197137/500000) 320 276
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t226 : ((33250919049/500000000000 : ℚ) : ℝ) ≤ stT320 226 := by
  have hc : ((499871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33250919049/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((499871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c227 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((6987/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3576493/10000000) (δ := 801/50000000) (ψ := 197137/500000) 320 276
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t227 : ((2317056993/250000000000 : ℚ) : ℝ) ≤ stT320 227 := by
  have hc : ((3491/25000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2317056993/250000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((3491/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c228 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-477013/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7092973/10000000) (δ := 801/50000000) (ψ := 197137/500000) 320 276
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t228 : ((-315943081821/5000000000000 : ℚ) : ℝ) ≤ stT320 228 := by
  have hc : ((-477063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315943081821/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-477063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c229 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-228559/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -511387/1000000) (δ := 1609/100000000) (ψ := 197137/500000) 320 277
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t229 : ((-151069170771/5000000000000 : ℚ) : ℝ) ≤ stT320 229 := by
  have hc : ((-228609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151069170771/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-228609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c230 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((15907/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162803/1000000) (δ := 1609/100000000) (ψ := 197137/500000) 320 277
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t230 : ((104874389/2000000000 : ℚ) : ℝ) ≤ stT320 230 := by
  have hc : ((3181/4000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104874389/2000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((3181/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c231 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((740437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184269/1000000) (δ := 1609/100000000) (ψ := 197137/500000) 320 277
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t231 : ((487105469487/10000000000000 : ℚ) : ℝ) ≤ stT320 231 := by
  have hc : ((740337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487105469487/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((740337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c232 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-130363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529837/1000000) (δ := 1609/100000000) (ψ := 197137/500000) 320 277
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t232 : ((-21401006201/625000000000 : ℚ) : ℝ) ≤ stT320 232 := by
  have hc : ((-32597/62500 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21401006201/625000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-32597/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c233 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-234489/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6968713/10000000) (δ := 16197/1000000000) (ψ := 197137/500000) 320 278
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t233 : ((-38408820177/625000000000 : ℚ) : ℝ) ≤ stT320 233 := by
  have hc : ((-117257/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38408820177/625000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-117257/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c234 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((15317/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3542553/10000000) (δ := 16197/1000000000) (ψ := 197137/500000) 320 278
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t234 : ((250162301/25000000000 : ℚ) : ℝ) ≤ stT320 234 := by
  have hc : ((15307/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250162301/25000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((15307/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c235 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((998627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131033/10000000) (δ := 16197/1000000000) (ψ := 197137/500000) 320 278
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t235 : ((81420890107/1250000000000 : ℚ) : ℝ) ≤ stT320 235 := by
  have hc : ((998527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81420890107/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((998527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c236 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((65331/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3266007/10000000) (δ := 16197/1000000000) (ψ := 197137/500000) 320 278
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t236 : ((332113663/19531250000 : ℚ) : ℝ) ≤ stT320 236 := by
  have hc : ((32653/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332113663/19531250000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((32653/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c237 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-110751/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6648647/10000000) (δ := 16197/1000000000) (ψ := 197137/500000) 320 278
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t237 : ((-14389729339/250000000000 : ℚ) : ℝ) ≤ stT320 237 := by
  have hc : ((-221527/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14389729339/250000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-221527/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c238 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-162117/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5690917/10000000) (δ := 8049/500000000) (ψ := 197137/500000) 320 279
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t238 : ((-13137636621/312500000000 : ℚ) : ℝ) ≤ stT320 238 := by
  have hc : ((-81071/125000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13137636621/312500000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-81071/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c239 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((594109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2336597/10000000) (δ := 8049/500000000) (ψ := 197137/500000) 320 279
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t239 : ((192116172807/5000000000000 : ℚ) : ℝ) ≤ stT320 239 := by
  have hc : ((594009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192116172807/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((594009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c240 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((5753/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1003723/10000000) (δ := 8049/500000000) (ψ := 197137/500000) 320 279
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t240 : ((29705126443/500000000000 : ℚ) : ℝ) ≤ stT320 240 := by
  have hc : ((46019/50000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29705126443/500000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((46019/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c241 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-32111/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4330123/10000000) (δ := 8049/500000000) (ψ := 197137/500000) 320 279
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t241 : ((-20697408567/2000000000000 : ℚ) : ℝ) ≤ stT320 241 := by
  have hc : ((-32131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20697408567/2000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-32131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c242 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-996433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7642763/10000000) (δ := 8049/500000000) (ψ := 197137/500000) 320 279
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t242 : ((-25623853029/400000000000 : ℚ) : ℝ) ≤ stT320 242 := by
  have hc : ((-996533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25623853029/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-996533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c243 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-32943/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29789/62500) (δ := 4003/250000000) (ψ := 197137/500000) 320 280
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t243 : ((-21139382453/1000000000000 : ℚ) : ℝ) ≤ stT320 243 := by
  have hc : ((-32953/100000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21139382453/1000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-32953/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c244 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((51853/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1851/12500) (δ := 4003/250000000) (ψ := 197137/500000) 320 280
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t244 : ((16595729901/312500000000 : ℚ) : ℝ) ≤ stT320 244 := by
  have hc : ((207387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16595729901/312500000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((207387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c245 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((754133/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44779/250000) (δ := 8003/250000000) (ψ := 197137/500000) 320 280
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t245 : ((120433396727/2500000000000 : ℚ) : ℝ) ≤ stT320 245 := by
  have hc : ((754033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120433396727/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((754033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c246 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-434191/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63123/125000) (δ := 4003/250000000) (ψ := 197137/500000) 320 280
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t246 : ((-276893952907/10000000000000 : ℚ) : ℝ) ≤ stT320 246 := by
  have hc : ((-434291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276893952907/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-434291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c247 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-984461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7412683/10000000) (δ := 16119/1000000000) (ψ := 197137/500000) 320 281
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t247 : ((-125292279177/2000000000000 : ℚ) : ℝ) ≤ stT320 247 := by
  have hc : ((-984561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125292279177/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-984561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c248 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((-4047/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4180363/10000000) (δ := 16119/1000000000) (ψ := 197137/500000) 320 281
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t248 : ((-2572389051/400000000000 : ℚ) : ℝ) ≤ stT320 248 := by
  have hc : ((-4051/40000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2572389051/400000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-4051/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c249 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((927011/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -961083/10000000) (δ := 16119/1000000000) (ψ := 197137/500000) 320 281
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t249 : ((146851436641/2500000000000 : ℚ) : ℝ) ≤ stT320 249 := by
  have hc : ((926911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146851436641/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((926911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_c250 :
    |Real.cos (((320 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((623051/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2245397/10000000) (δ := 16119/1000000000) (ψ := 197137/500000) 320 281
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st320_t250 : ((78797694941/2000000000000 : ℚ) : ℝ) ≤ stT320 250 := by
  have hc : ((622951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((320 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((197137/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st320_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78797694941/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((622951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st320_p1 : ((115397/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT320 (i+1) := by
  rw [Finset.sum_range_one]
  exact st320_t1

theorem st320_p2 : ((151904215561/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT320 (i+1))
      = (∑ i ∈ Finset.range 1, stT320 (i+1)) + stT320 2 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 1
    simpa using h
  have hprev := st320_p1
  have hstep := st320_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p3 : ((1768655645449/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT320 (i+1))
      = (∑ i ∈ Finset.range 2, stT320 (i+1)) + stT320 3 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 2
    simpa using h
  have hprev := st320_p2
  have hstep := st320_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p4 : ((4655437097959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT320 (i+1))
      = (∑ i ∈ Finset.range 3, stT320 (i+1)) + stT320 4 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 3
    simpa using h
  have hprev := st320_p3
  have hstep := st320_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p5 : ((3253300677457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT320 (i+1))
      = (∑ i ∈ Finset.range 4, stT320 (i+1)) + stT320 5 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 4
    simpa using h
  have hprev := st320_p4
  have hstep := st320_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p6 : ((7248174004009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT320 (i+1))
      = (∑ i ∈ Finset.range 5, stT320 (i+1)) + stT320 6 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 5
    simpa using h
  have hprev := st320_p5
  have hstep := st320_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p7 : ((9073496379149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT320 (i+1))
      = (∑ i ∈ Finset.range 6, stT320 (i+1)) + stT320 7 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 6
    simpa using h
  have hprev := st320_p6
  have hstep := st320_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p8 : ((20084715865141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT320 (i+1))
      = (∑ i ∈ Finset.range 7, stT320 (i+1)) + stT320 8 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 7
    simpa using h
  have hprev := st320_p7
  have hstep := st320_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p9 : ((5471928087877/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT320 (i+1))
      = (∑ i ∈ Finset.range 8, stT320 (i+1)) + stT320 9 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 8
    simpa using h
  have hprev := st320_p8
  have hstep := st320_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p10 : ((22732505165227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT320 (i+1))
      = (∑ i ∈ Finset.range 9, stT320 (i+1)) + stT320 10 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 9
    simpa using h
  have hprev := st320_p9
  have hstep := st320_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p11 : ((25528190301539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT320 (i+1))
      = (∑ i ∈ Finset.range 10, stT320 (i+1)) + stT320 11 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 10
    simpa using h
  have hprev := st320_p10
  have hstep := st320_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p12 : ((4528869629511/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT320 (i+1))
      = (∑ i ∈ Finset.range 11, stT320 (i+1)) + stT320 12 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 11
    simpa using h
  have hprev := st320_p11
  have hstep := st320_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p13 : ((4025501386019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT320 (i+1))
      = (∑ i ∈ Finset.range 12, stT320 (i+1)) + stT320 13 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 12
    simpa using h
  have hprev := st320_p12
  have hstep := st320_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p14 : ((18648194253691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT320 (i+1))
      = (∑ i ∈ Finset.range 13, stT320 (i+1)) + stT320 14 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 13
    simpa using h
  have hprev := st320_p13
  have hstep := st320_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p15 : ((4051487786119/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT320 (i+1))
      = (∑ i ∈ Finset.range 14, stT320 (i+1)) + stT320 15 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 14
    simpa using h
  have hprev := st320_p14
  have hstep := st320_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p16 : ((4360281286119/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT320 (i+1))
      = (∑ i ∈ Finset.range 15, stT320 (i+1)) + stT320 16 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 15
    simpa using h
  have hprev := st320_p15
  have hstep := st320_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p17 : ((22080627965451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT320 (i+1))
      = (∑ i ∈ Finset.range 16, stT320 (i+1)) + stT320 17 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 16
    simpa using h
  have hprev := st320_p16
  have hstep := st320_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p18 : ((23552093229831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT320 (i+1))
      = (∑ i ∈ Finset.range 17, stT320 (i+1)) + stT320 18 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 17
    simpa using h
  have hprev := st320_p17
  have hstep := st320_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p19 : ((12687986640279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT320 (i+1))
      = (∑ i ∈ Finset.range 18, stT320 (i+1)) + stT320 19 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 18
    simpa using h
  have hprev := st320_p18
  have hstep := st320_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p20 : ((11571487700961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT320 (i+1))
      = (∑ i ∈ Finset.range 19, stT320 (i+1)) + stT320 20 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 19
    simpa using h
  have hprev := st320_p19
  have hstep := st320_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p21 : ((3165389678731/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT320 (i+1))
      = (∑ i ∈ Finset.range 20, stT320 (i+1)) + stT320 21 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 20
    simpa using h
  have hprev := st320_p20
  have hstep := st320_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p22 : ((93499004703/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT320 (i+1))
      = (∑ i ∈ Finset.range 21, stT320 (i+1)) + stT320 22 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 21
    simpa using h
  have hprev := st320_p21
  have hstep := st320_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p23 : ((1404786088383/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT320 (i+1))
      = (∑ i ∈ Finset.range 22, stT320 (i+1)) + stT320 23 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 22
    simpa using h
  have hprev := st320_p22
  have hstep := st320_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p24 : ((11518018332463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT320 (i+1))
      = (∑ i ∈ Finset.range 23, stT320 (i+1)) + stT320 24 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 23
    simpa using h
  have hprev := st320_p23
  have hstep := st320_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p25 : ((12217208332463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT320 (i+1))
      = (∑ i ∈ Finset.range 24, stT320 (i+1)) + stT320 25 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 24
    simpa using h
  have hprev := st320_p24
  have hstep := st320_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p26 : ((12891698668227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT320 (i+1))
      = (∑ i ∈ Finset.range 25, stT320 (i+1)) + stT320 26 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 25
    simpa using h
  have hprev := st320_p25
  have hstep := st320_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p27 : ((13147507057227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT320 (i+1))
      = (∑ i ∈ Finset.range 26, stT320 (i+1)) + stT320 27 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 26
    simpa using h
  have hprev := st320_p26
  have hstep := st320_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p28 : ((25136853097311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT320 (i+1))
      = (∑ i ∈ Finset.range 27, stT320 (i+1)) + stT320 28 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 27
    simpa using h
  have hprev := st320_p27
  have hstep := st320_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p29 : ((23445585817961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT320 (i+1))
      = (∑ i ∈ Finset.range 28, stT320 (i+1)) + stT320 29 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 28
    simpa using h
  have hprev := st320_p28
  have hstep := st320_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p30 : ((763600041903/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT320 (i+1))
      = (∑ i ∈ Finset.range 29, stT320 (i+1)) + stT320 30 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 29
    simpa using h
  have hprev := st320_p29
  have hstep := st320_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p31 : ((790257060529/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT320 (i+1))
      = (∑ i ∈ Finset.range 30, stT320 (i+1)) + stT320 31 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 30
    simpa using h
  have hprev := st320_p30
  have hstep := st320_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p32 : ((4724410854837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT320 (i+1))
      = (∑ i ∈ Finset.range 31, stT320 (i+1)) + stT320 32 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 31
    simpa using h
  have hprev := st320_p31
  have hstep := st320_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p33 : ((25356927302769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT320 (i+1))
      = (∑ i ∈ Finset.range 32, stT320 (i+1)) + stT320 33 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 32
    simpa using h
  have hprev := st320_p32
  have hstep := st320_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p34 : ((23679211378521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT320 (i+1))
      = (∑ i ∈ Finset.range 33, stT320 (i+1)) + stT320 34 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 33
    simpa using h
  have hprev := st320_p33
  have hstep := st320_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p35 : ((25366252013157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT320 (i+1))
      = (∑ i ∈ Finset.range 34, stT320 (i+1)) + stT320 35 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 34
    simpa using h
  have hprev := st320_p34
  have hstep := st320_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p36 : ((23800195033279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT320 (i+1))
      = (∑ i ∈ Finset.range 35, stT320 (i+1)) + stT320 36 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 35
    simpa using h
  have hprev := st320_p35
  have hstep := st320_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p37 : ((12339548106257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT320 (i+1))
      = (∑ i ∈ Finset.range 36, stT320 (i+1)) + stT320 37 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 36
    simpa using h
  have hprev := st320_p36
  have hstep := st320_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p38 : ((251996630629/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT320 (i+1))
      = (∑ i ∈ Finset.range 37, stT320 (i+1)) + stT320 38 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 37
    simpa using h
  have hprev := st320_p37
  have hstep := st320_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p39 : ((1180601199277/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT320 (i+1))
      = (∑ i ∈ Finset.range 38, stT320 (i+1)) + stT320 39 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 38
    simpa using h
  have hprev := st320_p38
  have hstep := st320_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p40 : ((12098516988787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT320 (i+1))
      = (∑ i ∈ Finset.range 39, stT320 (i+1)) + stT320 40 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 39
    simpa using h
  have hprev := st320_p39
  have hstep := st320_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p41 : ((12809272867909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT320 (i+1))
      = (∑ i ∈ Finset.range 40, stT320 (i+1)) + stT320 41 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 40
    simpa using h
  have hprev := st320_p40
  have hstep := st320_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p42 : ((1259301125219/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT320 (i+1))
      = (∑ i ∈ Finset.range 41, stT320 (i+1)) + stT320 42 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 41
    simpa using h
  have hprev := st320_p41
  have hstep := st320_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p43 : ((5915529048617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT320 (i+1))
      = (∑ i ∈ Finset.range 42, stT320 (i+1)) + stT320 43 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 42
    simpa using h
  have hprev := st320_p42
  have hstep := st320_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p44 : ((22890040475159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT320 (i+1))
      = (∑ i ∈ Finset.range 43, stT320 (i+1)) + stT320 44 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 43
    simpa using h
  have hprev := st320_p43
  have hstep := st320_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p45 : ((23429728541333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT320 (i+1))
      = (∑ i ∈ Finset.range 44, stT320 (i+1)) + stT320 45 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 44
    simpa using h
  have hprev := st320_p44
  have hstep := st320_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p46 : ((24757103734463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT320 (i+1))
      = (∑ i ∈ Finset.range 45, stT320 (i+1)) + stT320 46 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 45
    simpa using h
  have hprev := st320_p45
  have hstep := st320_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p47 : ((13099759714871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT320 (i+1))
      = (∑ i ∈ Finset.range 46, stT320 (i+1)) + stT320 47 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 46
    simpa using h
  have hprev := st320_p46
  have hstep := st320_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p48 : ((27388555877617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT320 (i+1))
      = (∑ i ∈ Finset.range 47, stT320 (i+1)) + stT320 48 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 47
    simpa using h
  have hprev := st320_p47
  have hstep := st320_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p49 : ((14128345665731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT320 (i+1))
      = (∑ i ∈ Finset.range 48, stT320 (i+1)) + stT320 49 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 48
    simpa using h
  have hprev := st320_p48
  have hstep := st320_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p50 : ((722475176927/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT320 (i+1))
      = (∑ i ∈ Finset.range 49, stT320 (i+1)) + stT320 50 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 49
    simpa using h
  have hprev := st320_p49
  have hstep := st320_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p51 : ((29467190291/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT320 (i+1))
      = (∑ i ∈ Finset.range 50, stT320 (i+1)) + stT320 51 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 50
    simpa using h
  have hprev := st320_p50
  have hstep := st320_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p52 : ((120465628043/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT320 (i+1))
      = (∑ i ∈ Finset.range 51, stT320 (i+1)) + stT320 52 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 51
    simpa using h
  have hprev := st320_p51
  have hstep := st320_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p53 : ((96795984637/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT320 (i+1))
      = (∑ i ∈ Finset.range 52, stT320 (i+1)) + stT320 53 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 52
    simpa using h
  have hprev := st320_p52
  have hstep := st320_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p54 : ((16051152250501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT320 (i+1))
      = (∑ i ∈ Finset.range 53, stT320 (i+1)) + stT320 54 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 53
    simpa using h
  have hprev := st320_p53
  have hstep := st320_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p55 : ((6685633541703/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT320 (i+1))
      = (∑ i ∈ Finset.range 54, stT320 (i+1)) + stT320 55 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 54
    simpa using h
  have hprev := st320_p54
  have hstep := st320_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p56 : ((34690172422303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT320 (i+1))
      = (∑ i ∈ Finset.range 55, stT320 (i+1)) + stT320 56 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 55
    simpa using h
  have hprev := st320_p55
  have hstep := st320_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p57 : ((7091226146891/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT320 (i+1))
      = (∑ i ∈ Finset.range 56, stT320 (i+1)) + stT320 57 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 56
    simpa using h
  have hprev := st320_p56
  have hstep := st320_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p58 : ((7064705385247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT320 (i+1))
      = (∑ i ∈ Finset.range 57, stT320 (i+1)) + stT320 58 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 57
    simpa using h
  have hprev := st320_p57
  have hstep := st320_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p59 : ((6858466480897/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT320 (i+1))
      = (∑ i ∈ Finset.range 58, stT320 (i+1)) + stT320 59 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 58
    simpa using h
  have hprev := st320_p58
  have hstep := st320_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p60 : ((1652037767741/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT320 (i+1))
      = (∑ i ∈ Finset.range 59, stT320 (i+1)) + stT320 60 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 59
    simpa using h
  have hprev := st320_p59
  have hstep := st320_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p61 : ((16313573756899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT320 (i+1))
      = (∑ i ∈ Finset.range 60, stT320 (i+1)) + stT320 61 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 60
    simpa using h
  have hprev := st320_p60
  have hstep := st320_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p62 : ((33493624746063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT320 (i+1))
      = (∑ i ∈ Finset.range 61, stT320 (i+1)) + stT320 62 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 61
    simpa using h
  have hprev := st320_p61
  have hstep := st320_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p63 : ((8669971149957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT320 (i+1))
      = (∑ i ∈ Finset.range 62, stT320 (i+1)) + stT320 63 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 62
    simpa using h
  have hprev := st320_p62
  have hstep := st320_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p64 : ((17329763541771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT320 (i+1))
      = (∑ i ∈ Finset.range 63, stT320 (i+1)) + stT320 64 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 63
    simpa using h
  have hprev := st320_p63
  have hstep := st320_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p65 : ((16726252376803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT320 (i+1))
      = (∑ i ∈ Finset.range 64, stT320 (i+1)) + stT320 65 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 64
    simpa using h
  have hprev := st320_p64
  have hstep := st320_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p66 : ((32966269941221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT320 (i+1))
      = (∑ i ∈ Finset.range 65, stT320 (i+1)) + stT320 66 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 65
    simpa using h
  have hprev := st320_p65
  have hstep := st320_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p67 : ((34034918668759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT320 (i+1))
      = (∑ i ∈ Finset.range 66, stT320 (i+1)) + stT320 67 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 66
    simpa using h
  have hprev := st320_p66
  have hstep := st320_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p68 : ((34652194811641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT320 (i+1))
      = (∑ i ∈ Finset.range 67, stT320 (i+1)) + stT320 68 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 67
    simpa using h
  have hprev := st320_p67
  have hstep := st320_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p69 : ((16795898038547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT320 (i+1))
      = (∑ i ∈ Finset.range 68, stT320 (i+1)) + stT320 69 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 68
    simpa using h
  have hprev := st320_p68
  have hstep := st320_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p70 : ((2071398327493/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT320 (i+1))
      = (∑ i ∈ Finset.range 69, stT320 (i+1)) + stT320 70 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 69
    simpa using h
  have hprev := st320_p69
  have hstep := st320_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p71 : ((17151224646913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT320 (i+1))
      = (∑ i ∈ Finset.range 70, stT320 (i+1)) + stT320 71 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 70
    simpa using h
  have hprev := st320_p70
  have hstep := st320_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p72 : ((17136608741089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT320 (i+1))
      = (∑ i ∈ Finset.range 71, stT320 (i+1)) + stT320 72 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 71
    simpa using h
  have hprev := st320_p71
  have hstep := st320_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p73 : ((16581651454023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT320 (i+1))
      = (∑ i ∈ Finset.range 72, stT320 (i+1)) + stT320 73 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 72
    simpa using h
  have hprev := st320_p72
  have hstep := st320_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p74 : ((16947901142583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT320 (i+1))
      = (∑ i ∈ Finset.range 73, stT320 (i+1)) + stT320 74 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 73
    simpa using h
  have hprev := st320_p73
  have hstep := st320_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p75 : ((17210326924833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT320 (i+1))
      = (∑ i ∈ Finset.range 74, stT320 (i+1)) + stT320 75 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 74
    simpa using h
  have hprev := st320_p74
  have hstep := st320_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p76 : ((8318365608981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT320 (i+1))
      = (∑ i ∈ Finset.range 75, stT320 (i+1)) + stT320 76 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 75
    simpa using h
  have hprev := st320_p75
  have hstep := st320_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p77 : ((33850714533809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT320 (i+1))
      = (∑ i ∈ Finset.range 76, stT320 (i+1)) + stT320 77 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 76
    simpa using h
  have hprev := st320_p76
  have hstep := st320_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p78 : ((8587357899961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT320 (i+1))
      = (∑ i ∈ Finset.range 77, stT320 (i+1)) + stT320 78 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 77
    simpa using h
  have hprev := st320_p77
  have hstep := st320_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p79 : ((8310586533233/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT320 (i+1))
      = (∑ i ∈ Finset.range 78, stT320 (i+1)) + stT320 79 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 78
    simpa using h
  have hprev := st320_p78
  have hstep := st320_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p80 : ((1065453604927/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT320 (i+1))
      = (∑ i ∈ Finset.range 79, stT320 (i+1)) + stT320 80 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 79
    simpa using h
  have hprev := st320_p79
  have hstep := st320_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p81 : ((212859109689/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT320 (i+1))
      = (∑ i ∈ Finset.range 80, stT320 (i+1)) + stT320 81 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 80
    simpa using h
  have hprev := st320_p80
  have hstep := st320_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p82 : ((1665166283771/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT320 (i+1))
      = (∑ i ∈ Finset.range 81, stT320 (i+1)) + stT320 82 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 81
    simpa using h
  have hprev := st320_p81
  have hstep := st320_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p83 : ((17198586563513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT320 (i+1))
      = (∑ i ∈ Finset.range 82, stT320 (i+1)) + stT320 83 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 82
    simpa using h
  have hprev := st320_p82
  have hstep := st320_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p84 : ((16751007261343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT320 (i+1))
      = (∑ i ∈ Finset.range 83, stT320 (i+1)) + stT320 84 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 83
    simpa using h
  have hprev := st320_p83
  have hstep := st320_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p85 : ((16919773689283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT320 (i+1))
      = (∑ i ∈ Finset.range 84, stT320 (i+1)) + stT320 85 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 84
    simpa using h
  have hprev := st320_p84
  have hstep := st320_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p86 : ((3414218200777/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT320 (i+1))
      = (∑ i ∈ Finset.range 85, stT320 (i+1)) + stT320 86 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 85
    simpa using h
  have hprev := st320_p85
  have hstep := st320_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p87 : ((33341966513587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT320 (i+1))
      = (∑ i ∈ Finset.range 86, stT320 (i+1)) + stT320 87 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 86
    simpa using h
  have hprev := st320_p86
  have hstep := st320_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p88 : ((34383833073661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT320 (i+1))
      = (∑ i ∈ Finset.range 87, stT320 (i+1)) + stT320 88 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 87
    simpa using h
  have hprev := st320_p87
  have hstep := st320_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p89 : ((33359770065859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT320 (i+1))
      = (∑ i ∈ Finset.range 88, stT320 (i+1)) + stT320 89 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 88
    simpa using h
  have hprev := st320_p88
  have hstep := st320_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p90 : ((34169008089271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT320 (i+1))
      = (∑ i ∈ Finset.range 89, stT320 (i+1)) + stT320 90 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 89
    simpa using h
  have hprev := st320_p89
  have hstep := st320_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p91 : ((33683842922141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT320 (i+1))
      = (∑ i ∈ Finset.range 90, stT320 (i+1)) + stT320 91 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 90
    simpa using h
  have hprev := st320_p90
  have hstep := st320_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p92 : ((6762817662877/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT320 (i+1))
      = (∑ i ∈ Finset.range 91, stT320 (i+1)) + stT320 92 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 91
    simpa using h
  have hprev := st320_p91
  have hstep := st320_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p93 : ((8503102075997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT320 (i+1))
      = (∑ i ∈ Finset.range 92, stT320 (i+1)) + stT320 93 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 92
    simpa using h
  have hprev := st320_p92
  have hstep := st320_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p94 : ((41927530219/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT320 (i+1))
      = (∑ i ∈ Finset.range 93, stT320 (i+1)) + stT320 94 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 93
    simpa using h
  have hprev := st320_p93
  have hstep := st320_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p95 : ((267320206047/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT320 (i+1))
      = (∑ i ∈ Finset.range 94, stT320 (i+1)) + stT320 95 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 94
    simpa using h
  have hprev := st320_p94
  have hstep := st320_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p96 : ((6680071174533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT320 (i+1))
      = (∑ i ∈ Finset.range 95, stT320 (i+1)) + stT320 96 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 95
    simpa using h
  have hprev := st320_p95
  have hstep := st320_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p97 : ((6861197732127/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT320 (i+1))
      = (∑ i ∈ Finset.range 96, stT320 (i+1)) + stT320 97 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 96
    simpa using h
  have hprev := st320_p96
  have hstep := st320_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p98 : ((16674868207281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT320 (i+1))
      = (∑ i ∈ Finset.range 97, stT320 (i+1)) + stT320 98 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 97
    simpa using h
  have hprev := st320_p97
  have hstep := st320_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p99 : ((17165083044327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT320 (i+1))
      = (∑ i ∈ Finset.range 98, stT320 (i+1)) + stT320 99 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 98
    simpa using h
  have hprev := st320_p98
  have hstep := st320_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p100 : ((16670409544327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT320 (i+1))
      = (∑ i ∈ Finset.range 99, stT320 (i+1)) + stT320 100 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 99
    simpa using h
  have hprev := st320_p99
  have hstep := st320_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p101 : ((34330354529081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT320 (i+1))
      = (∑ i ∈ Finset.range 100, stT320 (i+1)) + stT320 101 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 100
    simpa using h
  have hprev := st320_p100
  have hstep := st320_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p102 : ((33344395845269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT320 (i+1))
      = (∑ i ∈ Finset.range 101, stT320 (i+1)) + stT320 102 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 101
    simpa using h
  have hprev := st320_p101
  have hstep := st320_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p103 : ((8580842614637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT320 (i+1))
      = (∑ i ∈ Finset.range 102, stT320 (i+1)) + stT320 103 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 102
    simpa using h
  have hprev := st320_p102
  have hstep := st320_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p104 : ((16677806748433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT320 (i+1))
      = (∑ i ∈ Finset.range 103, stT320 (i+1)) + stT320 104 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 103
    simpa using h
  have hprev := st320_p103
  have hstep := st320_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p105 : ((17151503240983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT320 (i+1))
      = (∑ i ∈ Finset.range 104, stT320 (i+1)) + stT320 105 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 104
    simpa using h
  have hprev := st320_p104
  have hstep := st320_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p106 : ((16695302833501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT320 (i+1))
      = (∑ i ∈ Finset.range 105, stT320 (i+1)) + stT320 106 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 105
    simpa using h
  have hprev := st320_p105
  have hstep := st320_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p107 : ((3424478749473/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT320 (i+1))
      = (∑ i ∈ Finset.range 106, stT320 (i+1)) + stT320 107 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 106
    simpa using h
  have hprev := st320_p106
  have hstep := st320_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p108 : ((418497594653/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT320 (i+1))
      = (∑ i ∈ Finset.range 107, stT320 (i+1)) + stT320 108 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 107
    simpa using h
  have hprev := st320_p107
  have hstep := st320_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p109 : ((2132249246177/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT320 (i+1))
      = (∑ i ∈ Finset.range 108, stT320 (i+1)) + stT320 109 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 108
    simpa using h
  have hprev := st320_p108
  have hstep := st320_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p110 : ((16826318669287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT320 (i+1))
      = (∑ i ∈ Finset.range 109, stT320 (i+1)) + stT320 110 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 109
    simpa using h
  have hprev := st320_p109
  have hstep := st320_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p111 : ((33898137745781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT320 (i+1))
      = (∑ i ∈ Finset.range 110, stT320 (i+1)) + stT320 111 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 110
    simpa using h
  have hprev := st320_p110
  have hstep := st320_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p112 : ((33907409212513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT320 (i+1))
      = (∑ i ∈ Finset.range 111, stT320 (i+1)) + stT320 112 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 111
    simpa using h
  have hprev := st320_p111
  have hstep := st320_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p113 : ((33623006676909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT320 (i+1))
      = (∑ i ∈ Finset.range 112, stT320 (i+1)) + stT320 113 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 112
    simpa using h
  have hprev := st320_p112
  have hstep := st320_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p114 : ((4271763885753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT320 (i+1))
      = (∑ i ∈ Finset.range 113, stT320 (i+1)) + stT320 114 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 113
    simpa using h
  have hprev := st320_p113
  have hstep := st320_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p115 : ((16700820364557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT320 (i+1))
      = (∑ i ∈ Finset.range 114, stT320 (i+1)) + stT320 115 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 114
    simpa using h
  have hprev := st320_p114
  have hstep := st320_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p116 : ((17153441737083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT320 (i+1))
      = (∑ i ∈ Finset.range 115, stT320 (i+1)) + stT320 116 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 115
    simpa using h
  have hprev := st320_p115
  have hstep := st320_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p117 : ((33395781267159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT320 (i+1))
      = (∑ i ∈ Finset.range 116, stT320 (i+1)) + stT320 117 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 116
    simpa using h
  have hprev := st320_p116
  have hstep := st320_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p118 : ((34161033260157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT320 (i+1))
      = (∑ i ∈ Finset.range 117, stT320 (i+1)) + stT320 118 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 117
    simpa using h
  have hprev := st320_p117
  have hstep := st320_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p119 : ((421116444233/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT320 (i+1))
      = (∑ i ∈ Finset.range 118, stT320 (i+1)) + stT320 119 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 118
    simpa using h
  have hprev := st320_p118
  have hstep := st320_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p120 : ((843978569767/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT320 (i+1))
      = (∑ i ∈ Finset.range 119, stT320 (i+1)) + stT320 120 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 119
    simpa using h
  have hprev := st320_p119
  have hstep := st320_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p121 : ((26656912409/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT320 (i+1))
      = (∑ i ∈ Finset.range 120, stT320 (i+1)) + stT320 121 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 120
    simpa using h
  have hprev := st320_p120
  have hstep := st320_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p122 : ((16701011754167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT320 (i+1))
      = (∑ i ∈ Finset.range 121, stT320 (i+1)) + stT320 122 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 121
    simpa using h
  have hprev := st320_p121
  have hstep := st320_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p123 : ((34296644161761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT320 (i+1))
      = (∑ i ∈ Finset.range 122, stT320 (i+1)) + stT320 123 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 122
    simpa using h
  have hprev := st320_p122
  have hstep := st320_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p124 : ((8369712846019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT320 (i+1))
      = (∑ i ∈ Finset.range 123, stT320 (i+1)) + stT320 124 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 123
    simpa using h
  have hprev := st320_p123
  have hstep := st320_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p125 : ((16981966567201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT320 (i+1))
      = (∑ i ∈ Finset.range 124, stT320 (i+1)) + stT320 125 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 124
    simpa using h
  have hprev := st320_p124
  have hstep := st320_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p126 : ((8495065918093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT320 (i+1))
      = (∑ i ∈ Finset.range 125, stT320 (i+1)) + stT320 126 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 125
    simpa using h
  have hprev := st320_p125
  have hstep := st320_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p127 : ((16728555852369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT320 (i+1))
      = (∑ i ∈ Finset.range 126, stT320 (i+1)) + stT320 127 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 126
    simpa using h
  have hprev := st320_p126
  have hstep := st320_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p128 : ((6859828392161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT320 (i+1))
      = (∑ i ∈ Finset.range 127, stT320 (i+1)) + stT320 128 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 127
    simpa using h
  have hprev := st320_p127
  have hstep := st320_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p129 : ((33469787054139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT320 (i+1))
      = (∑ i ∈ Finset.range 128, stT320 (i+1)) + stT320 129 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 128
    simpa using h
  have hprev := st320_p128
  have hstep := st320_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p130 : ((33933788449633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT320 (i+1))
      = (∑ i ∈ Finset.range 129, stT320 (i+1)) + stT320 130 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 129
    simpa using h
  have hprev := st320_p129
  have hstep := st320_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p131 : ((34048586165601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT320 (i+1))
      = (∑ i ∈ Finset.range 130, stT320 (i+1)) + stT320 131 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 130
    simpa using h
  have hprev := st320_p130
  have hstep := st320_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p132 : ((33400372661741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT320 (i+1))
      = (∑ i ∈ Finset.range 131, stT320 (i+1)) + stT320 132 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 131
    simpa using h
  have hprev := st320_p131
  have hstep := st320_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p133 : ((1713369357343/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT320 (i+1))
      = (∑ i ∈ Finset.range 132, stT320 (i+1)) + stT320 133 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 132
    simpa using h
  have hprev := st320_p132
  have hstep := st320_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p134 : ((6725903847059/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT320 (i+1))
      = (∑ i ∈ Finset.range 133, stT320 (i+1)) + stT320 134 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 133
    simpa using h
  have hprev := st320_p133
  have hstep := st320_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p135 : ((33688012406801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT320 (i+1))
      = (∑ i ∈ Finset.range 134, stT320 (i+1)) + stT320 135 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 134
    simpa using h
  have hprev := st320_p134
  have hstep := st320_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p136 : ((6849613574349/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT320 (i+1))
      = (∑ i ∈ Finset.range 135, stT320 (i+1)) + stT320 136 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 135
    simpa using h
  have hprev := st320_p135
  have hstep := st320_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p137 : ((33395250279219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT320 (i+1))
      = (∑ i ∈ Finset.range 136, stT320 (i+1)) + stT320 137 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 136
    simpa using h
  have hprev := st320_p136
  have hstep := st320_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p138 : ((34016498610531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT320 (i+1))
      = (∑ i ∈ Finset.range 137, stT320 (i+1)) + stT320 138 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 137
    simpa using h
  have hprev := st320_p137
  have hstep := st320_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p139 : ((6805474136863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT320 (i+1))
      = (∑ i ∈ Finset.range 138, stT320 (i+1)) + stT320 139 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 138
    simpa using h
  have hprev := st320_p138
  have hstep := st320_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p140 : ((1335458639339/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT320 (i+1))
      = (∑ i ∈ Finset.range 139, stT320 (i+1)) + stT320 140 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 139
    simpa using h
  have hprev := st320_p139
  have hstep := st320_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p141 : ((17109294745759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT320 (i+1))
      = (∑ i ∈ Finset.range 140, stT320 (i+1)) + stT320 141 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 140
    simpa using h
  have hprev := st320_p140
  have hstep := st320_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p142 : ((3378929419087/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT320 (i+1))
      = (∑ i ∈ Finset.range 141, stT320 (i+1)) + stT320 142 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 141
    simpa using h
  have hprev := st320_p141
  have hstep := st320_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p143 : ((523364839983/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT320 (i+1))
      = (∑ i ∈ Finset.range 142, stT320 (i+1)) + stT320 143 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 142
    simpa using h
  have hprev := st320_p142
  have hstep := st320_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p144 : ((8572839860127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT320 (i+1))
      = (∑ i ∈ Finset.range 143, stT320 (i+1)) + stT320 144 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 143
    simpa using h
  have hprev := st320_p143
  have hstep := st320_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p145 : ((33618756496453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT320 (i+1))
      = (∑ i ∈ Finset.range 144, stT320 (i+1)) + stT320 145 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 144
    simpa using h
  have hprev := st320_p144
  have hstep := st320_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p146 : ((33619983007063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT320 (i+1))
      = (∑ i ∈ Finset.range 145, stT320 (i+1)) + stT320 146 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 145
    simpa using h
  have hprev := st320_p145
  have hstep := st320_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p147 : ((34293528823029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT320 (i+1))
      = (∑ i ∈ Finset.range 146, stT320 (i+1)) + stT320 147 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 146
    simpa using h
  have hprev := st320_p146
  have hstep := st320_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p148 : ((33523283340249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT320 (i+1))
      = (∑ i ∈ Finset.range 147, stT320 (i+1)) + stT320 148 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 147
    simpa using h
  have hprev := st320_p147
  have hstep := st320_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p149 : ((33707654553723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT320 (i+1))
      = (∑ i ∈ Finset.range 148, stT320 (i+1)) + stT320 149 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 148
    simpa using h
  have hprev := st320_p148
  have hstep := st320_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p150 : ((6855665947199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT320 (i+1))
      = (∑ i ∈ Finset.range 149, stT320 (i+1)) + stT320 150 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 149
    simpa using h
  have hprev := st320_p149
  have hstep := st320_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p151 : ((16741910105597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT320 (i+1))
      = (∑ i ∈ Finset.range 150, stT320 (i+1)) + stT320 151 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 150
    simpa using h
  have hprev := st320_p150
  have hstep := st320_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p152 : ((16870543564727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT320 (i+1))
      = (∑ i ∈ Finset.range 151, stT320 (i+1)) + stT320 152 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 151
    simpa using h
  have hprev := st320_p151
  have hstep := st320_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p153 : ((17137154461061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT320 (i+1))
      = (∑ i ∈ Finset.range 152, stT320 (i+1)) + stT320 153 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 152
    simpa using h
  have hprev := st320_p152
  have hstep := st320_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p154 : ((33485518602873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT320 (i+1))
      = (∑ i ∈ Finset.range 153, stT320 (i+1)) + stT320 154 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 153
    simpa using h
  have hprev := st320_p153
  have hstep := st320_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p155 : ((33718156528281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT320 (i+1))
      = (∑ i ∈ Finset.range 154, stT320 (i+1)) + stT320 155 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 154
    simpa using h
  have hprev := st320_p154
  have hstep := st320_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p156 : ((34286677381401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT320 (i+1))
      = (∑ i ∈ Finset.range 155, stT320 (i+1)) + stT320 156 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 155
    simpa using h
  have hprev := st320_p155
  have hstep := st320_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p157 : ((33527982359547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT320 (i+1))
      = (∑ i ∈ Finset.range 156, stT320 (i+1)) + stT320 157 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 156
    simpa using h
  have hprev := st320_p156
  have hstep := st320_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p158 : ((33642956257187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT320 (i+1))
      = (∑ i ∈ Finset.range 157, stT320 (i+1)) + stT320 158 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 157
    simpa using h
  have hprev := st320_p157
  have hstep := st320_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p159 : ((686008116917/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT320 (i+1))
      = (∑ i ∈ Finset.range 158, stT320 (i+1)) + stT320 159 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 158
    simpa using h
  have hprev := st320_p158
  have hstep := st320_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p160 : ((3362308025493/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT320 (i+1))
      = (∑ i ∈ Finset.range 159, stT320 (i+1)) + stT320 160 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 159
    simpa using h
  have hprev := st320_p159
  have hstep := st320_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p161 : ((33529374645141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT320 (i+1))
      = (∑ i ∈ Finset.range 160, stT320 (i+1)) + stT320 161 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 160
    simpa using h
  have hprev := st320_p160
  have hstep := st320_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p162 : ((6856362298449/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT320 (i+1))
      = (∑ i ∈ Finset.range 161, stT320 (i+1)) + stT320 162 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 161
    simpa using h
  have hprev := st320_p161
  have hstep := st320_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p163 : ((2111446822491/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT320 (i+1))
      = (∑ i ∈ Finset.range 162, stT320 (i+1)) + stT320 163 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 162
    simpa using h
  have hprev := st320_p162
  have hstep := st320_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p164 : ((16706275147097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT320 (i+1))
      = (∑ i ∈ Finset.range 163, stT320 (i+1)) + stT320 164 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 163
    simpa using h
  have hprev := st320_p163
  have hstep := st320_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p165 : ((2136586253141/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT320 (i+1))
      = (∑ i ∈ Finset.range 164, stT320 (i+1)) + stT320 165 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 164
    simpa using h
  have hprev := st320_p164
  have hstep := st320_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p166 : ((16999338463603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT320 (i+1))
      = (∑ i ∈ Finset.range 165, stT320 (i+1)) + stT320 166 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 165
    simpa using h
  have hprev := st320_p165
  have hstep := st320_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p167 : ((16678659220499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT320 (i+1))
      = (∑ i ∈ Finset.range 166, stT320 (i+1)) + stT320 167 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 166
    simpa using h
  have hprev := st320_p166
  have hstep := st320_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p168 : ((16988685209939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT320 (i+1))
      = (∑ i ∈ Finset.range 167, stT320 (i+1)) + stT320 168 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 167
    simpa using h
  have hprev := st320_p167
  have hstep := st320_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p169 : ((8552775046537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT320 (i+1))
      = (∑ i ∈ Finset.range 168, stT320 (i+1)) + stT320 169 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 168
    simpa using h
  have hprev := st320_p168
  have hstep := st320_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p170 : ((16722042283229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT320 (i+1))
      = (∑ i ∈ Finset.range 169, stT320 (i+1)) + stT320 170 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 169
    simpa using h
  have hprev := st320_p169
  have hstep := st320_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p171 : ((842010677279/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT320 (i+1))
      = (∑ i ∈ Finset.range 170, stT320 (i+1)) + stT320 171 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 170
    simpa using h
  have hprev := st320_p170
  have hstep := st320_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p172 : ((4288198522753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT320 (i+1))
      = (∑ i ∈ Finset.range 171, stT320 (i+1)) + stT320 172 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 171
    simpa using h
  have hprev := st320_p171
  have hstep := st320_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p173 : ((4214120056343/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT320 (i+1))
      = (∑ i ∈ Finset.range 172, stT320 (i+1)) + stT320 173 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 172
    simpa using h
  have hprev := st320_p172
  have hstep := st320_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p174 : ((16707600953257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT320 (i+1))
      = (∑ i ∈ Finset.range 173, stT320 (i+1)) + stT320 174 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 173
    simpa using h
  have hprev := st320_p173
  have hstep := st320_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p175 : ((17081802321637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT320 (i+1))
      = (∑ i ∈ Finset.range 174, stT320 (i+1)) + stT320 175 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 174
    simpa using h
  have hprev := st320_p174
  have hstep := st320_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p176 : ((17039619341239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT320 (i+1))
      = (∑ i ∈ Finset.range 175, stT320 (i+1)) + stT320 176 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 175
    simpa using h
  have hprev := st320_p175
  have hstep := st320_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p177 : ((3337420582283/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT320 (i+1))
      = (∑ i ∈ Finset.range 176, stT320 (i+1)) + stT320 177 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 176
    simpa using h
  have hprev := st320_p176
  have hstep := st320_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p178 : ((4223607108183/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT320 (i+1))
      = (∑ i ∈ Finset.range 177, stT320 (i+1)) + stT320 178 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 177
    simpa using h
  have hprev := st320_p177
  have hstep := st320_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p179 : ((17152534929237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT320 (i+1))
      = (∑ i ∈ Finset.range 178, stT320 (i+1)) + stT320 179 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 178
    simpa using h
  have hprev := st320_p178
  have hstep := st320_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p180 : ((16834896625023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT320 (i+1))
      = (∑ i ∈ Finset.range 179, stT320 (i+1)) + stT320 180 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 179
    simpa using h
  have hprev := st320_p179
  have hstep := st320_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p181 : ((33415872528621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT320 (i+1))
      = (∑ i ∈ Finset.range 180, stT320 (i+1)) + stT320 181 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 180
    simpa using h
  have hprev := st320_p180
  have hstep := st320_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p182 : ((17074008383577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT320 (i+1))
      = (∑ i ∈ Finset.range 181, stT320 (i+1)) + stT320 182 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 181
    simpa using h
  have hprev := st320_p181
  have hstep := st320_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p183 : ((17064218127409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT320 (i+1))
      = (∑ i ∈ Finset.range 182, stT320 (i+1)) + stT320 183 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 182
    simpa using h
  have hprev := st320_p182
  have hstep := st320_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p184 : ((16702884966849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT320 (i+1))
      = (∑ i ∈ Finset.range 183, stT320 (i+1)) + stT320 184 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 183
    simpa using h
  have hprev := st320_p183
  have hstep := st320_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p185 : ((16833413389981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT320 (i+1))
      = (∑ i ∈ Finset.range 184, stT320 (i+1)) + stT320 185 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 184
    simpa using h
  have hprev := st320_p184
  have hstep := st320_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p186 : ((34304027792307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT320 (i+1))
      = (∑ i ∈ Finset.range 185, stT320 (i+1)) + stT320 186 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 185
    simpa using h
  have hprev := st320_p185
  have hstep := st320_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p187 : ((33854210069639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT320 (i+1))
      = (∑ i ∈ Finset.range 186, stT320 (i+1)) + stT320 187 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 186
    simpa using h
  have hprev := st320_p186
  have hstep := st320_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p188 : ((33345104753389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT320 (i+1))
      = (∑ i ∈ Finset.range 187, stT320 (i+1)) + stT320 188 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 187
    simpa using h
  have hprev := st320_p187
  have hstep := st320_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p189 : ((33925986911533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT320 (i+1))
      = (∑ i ∈ Finset.range 188, stT320 (i+1)) + stT320 189 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 188
    simpa using h
  have hprev := st320_p188
  have hstep := st320_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p190 : ((34291320664661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT320 (i+1))
      = (∑ i ∈ Finset.range 189, stT320 (i+1)) + stT320 190 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 189
    simpa using h
  have hprev := st320_p189
  have hstep := st320_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p191 : ((16815109203293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT320 (i+1))
      = (∑ i ∈ Finset.range 190, stT320 (i+1)) + stT320 191 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 190
    simpa using h
  have hprev := st320_p190
  have hstep := st320_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p192 : ((16702033684077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT320 (i+1))
      = (∑ i ∈ Finset.range 191, stT320 (i+1)) + stT320 192 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 191
    simpa using h
  have hprev := st320_p191
  have hstep := st320_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p193 : ((4263166232043/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT320 (i+1))
      = (∑ i ∈ Finset.range 192, stT320 (i+1)) + stT320 193 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 192
    simpa using h
  have hprev := st320_p192
  have hstep := st320_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p194 : ((8552093874063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT320 (i+1))
      = (∑ i ∈ Finset.range 193, stT320 (i+1)) + stT320 194 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 193
    simpa using h
  have hprev := st320_p193
  have hstep := st320_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p195 : ((16746963089871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT320 (i+1))
      = (∑ i ∈ Finset.range 194, stT320 (i+1)) + stT320 195 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 194
    simpa using h
  have hprev := st320_p194
  have hstep := st320_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p196 : ((209320355581/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT320 (i+1))
      = (∑ i ∈ Finset.range 195, stT320 (i+1)) + stT320 196 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 195
    simpa using h
  have hprev := st320_p195
  have hstep := st320_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p197 : ((1710130700741/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT320 (i+1))
      = (∑ i ∈ Finset.range 196, stT320 (i+1)) + stT320 197 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 196
    simpa using h
  have hprev := st320_p196
  have hstep := st320_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p198 : ((3412909307131/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT320 (i+1))
      = (∑ i ∈ Finset.range 197, stT320 (i+1)) + stT320 198 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 197
    simpa using h
  have hprev := st320_p197
  have hstep := st320_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p199 : ((8356890721633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT320 (i+1))
      = (∑ i ∈ Finset.range 198, stT320 (i+1)) + stT320 199 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 198
    simpa using h
  have hprev := st320_p198
  have hstep := st320_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p200 : ((4194090257843/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT320 (i+1))
      = (∑ i ∈ Finset.range 199, stT320 (i+1)) + stT320 200 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 199
    simpa using h
  have hprev := st320_p199
  have hstep := st320_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p201 : ((17121736737347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT320 (i+1))
      = (∑ i ∈ Finset.range 200, stT320 (i+1)) + stT320 201 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 200
    simpa using h
  have hprev := st320_p200
  have hstep := st320_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p202 : ((2130592707051/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT320 (i+1))
      = (∑ i ∈ Finset.range 201, stT320 (i+1)) + stT320 202 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 201
    simpa using h
  have hprev := st320_p201
  have hstep := st320_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p203 : ((33406033688621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT320 (i+1))
      = (∑ i ∈ Finset.range 202, stT320 (i+1)) + stT320 203 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 202
    simpa using h
  have hprev := st320_p202
  have hstep := st320_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p204 : ((33566730521561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT320 (i+1))
      = (∑ i ∈ Finset.range 203, stT320 (i+1)) + stT320 204 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 203
    simpa using h
  have hprev := st320_p203
  have hstep := st320_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p205 : ((34247378493761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT320 (i+1))
      = (∑ i ∈ Finset.range 204, stT320 (i+1)) + stT320 205 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 204
    simpa using h
  have hprev := st320_p204
  have hstep := st320_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p206 : ((34100651190499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT320 (i+1))
      = (∑ i ∈ Finset.range 205, stT320 (i+1)) + stT320 206 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 205
    simpa using h
  have hprev := st320_p205
  have hstep := st320_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p207 : ((208863506443/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT320 (i+1))
      = (∑ i ∈ Finset.range 206, stT320 (i+1)) + stT320 207 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 206
    simpa using h
  have hprev := st320_p206
  have hstep := st320_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p208 : ((6706025861201/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT320 (i+1))
      = (∑ i ∈ Finset.range 207, stT320 (i+1)) + stT320 208 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 207
    simpa using h
  have hprev := st320_p207
  have hstep := st320_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p209 : ((34216266016023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT320 (i+1))
      = (∑ i ∈ Finset.range 208, stT320 (i+1)) + stT320 209 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 208
    simpa using h
  have hprev := st320_p208
  have hstep := st320_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p210 : ((34159027111521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT320 (i+1))
      = (∑ i ∈ Finset.range 209, stT320 (i+1)) + stT320 210 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 209
    simpa using h
  have hprev := st320_p209
  have hstep := st320_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p211 : ((8367722329247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT320 (i+1))
      = (∑ i ∈ Finset.range 210, stT320 (i+1)) + stT320 211 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 210
    simpa using h
  have hprev := st320_p210
  have hstep := st320_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p212 : ((4181666485637/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT320 (i+1))
      = (∑ i ∈ Finset.range 211, stT320 (i+1)) + stT320 212 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 211
    simpa using h
  have hprev := st320_p211
  have hstep := st320_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p213 : ((8533913778517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT320 (i+1))
      = (∑ i ∈ Finset.range 212, stT320 (i+1)) + stT320 213 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 212
    simpa using h
  have hprev := st320_p212
  have hstep := st320_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p214 : ((34246061611003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT320 (i+1))
      = (∑ i ∈ Finset.range 213, stT320 (i+1)) + stT320 214 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 213
    simpa using h
  have hprev := st320_p213
  have hstep := st320_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p215 : ((8395938440167/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT320 (i+1))
      = (∑ i ∈ Finset.range 214, stT320 (i+1)) + stT320 215 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 214
    simpa using h
  have hprev := st320_p214
  have hstep := st320_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p216 : ((16682519721633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT320 (i+1))
      = (∑ i ∈ Finset.range 215, stT320 (i+1)) + stT320 216 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 215
    simpa using h
  have hprev := st320_p215
  have hstep := st320_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p217 : ((3398484505943/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT320 (i+1))
      = (∑ i ∈ Finset.range 216, stT320 (i+1)) + stT320 217 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 216
    simpa using h
  have hprev := st320_p216
  have hstep := st320_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p218 : ((3432097076837/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT320 (i+1))
      = (∑ i ∈ Finset.range 217, stT320 (i+1)) + stT320 218 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 217
    simpa using h
  have hprev := st320_p217
  have hstep := st320_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p219 : ((168865868113/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT320 (i+1))
      = (∑ i ∈ Finset.range 218, stT320 (i+1)) + stT320 219 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 218
    simpa using h
  have hprev := st320_p218
  have hstep := st320_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p220 : ((83297970607/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT320 (i+1))
      = (∑ i ∈ Finset.range 219, stT320 (i+1)) + stT320 220 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 219
    simpa using h
  have hprev := st320_p219
  have hstep := st320_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p221 : ((2109933634087/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT320 (i+1))
      = (∑ i ∈ Finset.range 220, stT320 (i+1)) + stT320 221 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 220
    simpa using h
  have hprev := st320_p220
  have hstep := st320_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p222 : ((1715892937049/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT320 (i+1))
      = (∑ i ∈ Finset.range 221, stT320 (i+1)) + stT320 222 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 221
    simpa using h
  have hprev := st320_p221
  have hstep := st320_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p223 : ((3402414958133/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT320 (i+1))
      = (∑ i ∈ Finset.range 222, stT320 (i+1)) + stT320 223 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 222
    simpa using h
  have hprev := st320_p222
  have hstep := st320_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p224 : ((16694392953517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT320 (i+1))
      = (∑ i ∈ Finset.range 223, stT320 (i+1)) + stT320 224 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 223
    simpa using h
  have hprev := st320_p223
  have hstep := st320_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p225 : ((837529828199/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT320 (i+1))
      = (∑ i ∈ Finset.range 224, stT320 (i+1)) + stT320 225 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 224
    simpa using h
  have hprev := st320_p224
  have hstep := st320_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p226 : ((1708310575447/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT320 (i+1))
      = (∑ i ∈ Finset.range 225, stT320 (i+1)) + stT320 226 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 225
    simpa using h
  have hprev := st320_p225
  have hstep := st320_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p227 : ((1712944689433/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT320 (i+1))
      = (∑ i ∈ Finset.range 226, stT320 (i+1)) + stT320 227 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 226
    simpa using h
  have hprev := st320_p226
  have hstep := st320_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p228 : ((16813503812509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT320 (i+1))
      = (∑ i ∈ Finset.range 227, stT320 (i+1)) + stT320 228 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 227
    simpa using h
  have hprev := st320_p227
  have hstep := st320_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p229 : ((8331217320869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT320 (i+1))
      = (∑ i ∈ Finset.range 228, stT320 (i+1)) + stT320 229 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 228
    simpa using h
  have hprev := st320_p228
  have hstep := st320_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p230 : ((8462310307119/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT320 (i+1))
      = (∑ i ∈ Finset.range 229, stT320 (i+1)) + stT320 230 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 229
    simpa using h
  have hprev := st320_p229
  have hstep := st320_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p231 : ((34336346697963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT320 (i+1))
      = (∑ i ∈ Finset.range 230, stT320 (i+1)) + stT320 231 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 230
    simpa using h
  have hprev := st320_p230
  have hstep := st320_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p232 : ((33993930598747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT320 (i+1))
      = (∑ i ∈ Finset.range 231, stT320 (i+1)) + stT320 232 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 231
    simpa using h
  have hprev := st320_p231
  have hstep := st320_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p233 : ((6675877895183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT320 (i+1))
      = (∑ i ∈ Finset.range 232, stT320 (i+1)) + stT320 233 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 232
    simpa using h
  have hprev := st320_p232
  have hstep := st320_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p234 : ((6695890879263/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT320 (i+1))
      = (∑ i ∈ Finset.range 233, stT320 (i+1)) + stT320 234 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 233
    simpa using h
  have hprev := st320_p233
  have hstep := st320_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p235 : ((34130821517171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT320 (i+1))
      = (∑ i ∈ Finset.range 234, stT320 (i+1)) + stT320 235 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 234
    simpa using h
  have hprev := st320_p234
  have hstep := st320_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p236 : ((34300863712627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT320 (i+1))
      = (∑ i ∈ Finset.range 235, stT320 (i+1)) + stT320 236 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 235
    simpa using h
  have hprev := st320_p235
  have hstep := st320_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p237 : ((33725274539067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT320 (i+1))
      = (∑ i ∈ Finset.range 236, stT320 (i+1)) + stT320 237 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 236
    simpa using h
  have hprev := st320_p236
  have hstep := st320_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p238 : ((6660974033439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT320 (i+1))
      = (∑ i ∈ Finset.range 237, stT320 (i+1)) + stT320 238 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 237
    simpa using h
  have hprev := st320_p237
  have hstep := st320_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p239 : ((33689102512809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT320 (i+1))
      = (∑ i ∈ Finset.range 238, stT320 (i+1)) + stT320 239 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 238
    simpa using h
  have hprev := st320_p238
  have hstep := st320_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p240 : ((34283205041669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT320 (i+1))
      = (∑ i ∈ Finset.range 239, stT320 (i+1)) + stT320 240 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 239
    simpa using h
  have hprev := st320_p239
  have hstep := st320_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p241 : ((17089858999417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT320 (i+1))
      = (∑ i ∈ Finset.range 240, stT320 (i+1)) + stT320 241 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 240
    simpa using h
  have hprev := st320_p240
  have hstep := st320_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p242 : ((33539121673109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT320 (i+1))
      = (∑ i ∈ Finset.range 241, stT320 (i+1)) + stT320 242 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 241
    simpa using h
  have hprev := st320_p241
  have hstep := st320_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p243 : ((33327727848579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT320 (i+1))
      = (∑ i ∈ Finset.range 242, stT320 (i+1)) + stT320 243 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 242
    simpa using h
  have hprev := st320_p242
  have hstep := st320_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p244 : ((33858791205411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT320 (i+1))
      = (∑ i ∈ Finset.range 243, stT320 (i+1)) + stT320 244 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 243
    simpa using h
  have hprev := st320_p243
  have hstep := st320_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p245 : ((34340524792319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT320 (i+1))
      = (∑ i ∈ Finset.range 244, stT320 (i+1)) + stT320 245 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 244
    simpa using h
  have hprev := st320_p244
  have hstep := st320_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p246 : ((8515907709853/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT320 (i+1))
      = (∑ i ∈ Finset.range 245, stT320 (i+1)) + stT320 246 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 245
    simpa using h
  have hprev := st320_p245
  have hstep := st320_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p247 : ((33437169443527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT320 (i+1))
      = (∑ i ∈ Finset.range 246, stT320 (i+1)) + stT320 247 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 246
    simpa using h
  have hprev := st320_p246
  have hstep := st320_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p248 : ((8343214929313/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT320 (i+1))
      = (∑ i ∈ Finset.range 247, stT320 (i+1)) + stT320 248 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 247
    simpa using h
  have hprev := st320_p247
  have hstep := st320_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p249 : ((4245033182977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT320 (i+1))
      = (∑ i ∈ Finset.range 248, stT320 (i+1)) + stT320 249 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 248
    simpa using h
  have hprev := st320_p248
  have hstep := st320_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_p250 : ((34354253938521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT320 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT320 (i+1))
      = (∑ i ∈ Finset.range 249, stT320 (i+1)) + stT320 250 := by
    have h := Finset.sum_range_succ (fun i => stT320 (i+1)) 249
    simpa using h
  have hprev := st320_p249
  have hstep := st320_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st320_s250 :
    |Real.sin (((320 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((197137/500000 : ℚ) : ℝ))
      - ((782181/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 2245397/10000000) (δ := 16119/1000000000) (ψ := 197137/500000) 320 281
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 320`** (evaluated boundary). -/
theorem station_320_sign : hardyG ((((320:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 320 250 (by norm_num) (by norm_num)
    ((197137/500000 : ℚ) : ℝ)
  have hchain := st320_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT320 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((320 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((197137/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st320_c250
  have hsinb := abs_le.mp st320_s250
  have hbdy_lo : ((-39629929419487/1024002500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((320 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((197137/500000 : ℚ) : ℝ))) / 2
          - ((((320:ℕ)):ℝ))
            * Real.sin (((320 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((197137/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((320:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((320:ℝ) * Real.log (250:ℝ) - ((197137/500000 : ℚ) : ℝ))) / 2
        - ((320:ℝ)) * Real.sin ((320:ℝ) * Real.log (250:ℝ) - ((197137/500000 : ℚ) : ℝ))
        ≥ ((-501282991/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((320:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-501282991/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-501282991/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-501282991/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((320:ℕ)):ℝ))+1) * (((((320:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((694925339317/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((34354253938521/10000000000000 : ℚ) : ℝ) + ((-39629929419487/1024002500000000 : ℚ) : ℝ)
      - ((694925339317/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((197137/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((320:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((197137/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((320:ℕ)):ℝ)))).re
      - Real.sin ((197137/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((320:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((320:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((320:ℕ)):ℝ))
      = (((((320:ℕ)):ℝ)) * (Real.log ((((320:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((320:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_320
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
  have hθwin : |(((197137/500000 : ℚ) : ℝ) + ((75:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((320:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((320:ℕ)):ℝ)))
    (φ := ((197137/500000 : ℚ) : ℝ) + ((75:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((197137/500000 : ℚ) : ℝ) + ((75:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((197137/500000 : ℚ)) : ℝ) - Real.pi) + ((75:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((197137/500000 : ℚ)) : ℝ) - Real.pi) 75).1,
    (cos_sin_shift ((((197137/500000 : ℚ)) : ℝ) - Real.pi) 75).2]
  exact cos_sin_flip ((197137/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_320_sign
end AxiomAudit
