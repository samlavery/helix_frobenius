import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 233` (rung-235.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT233 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((233 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-136127/200000 : ℚ) : ℝ))

theorem st233_c1 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((777173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 425397/2500000) (δ := 201/1000000000) (ψ := -136127/200000) 233 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t1 : ((777123/1000000 : ℚ) : ℝ) ≤ stT233 1 := by
  have hc : ((777123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((777123/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((777123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c2 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((47743/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2947243/10000000) (δ := 2363/200000000) (ψ := -136127/200000) 233 26
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t2 : ((1350199030449/5000000000000 : ℚ) : ℝ) ≤ stT233 2 := by
  have hc : ((190947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1350199030449/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((190947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c3 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((578989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383271/10000000) (δ := 11707/1000000000) (ψ := -136127/200000) 233 41
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t3 : ((1671252737189/5000000000000 : ℚ) : ℝ) ≤ stT233 3 := by
  have hc : ((578939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1671252737189/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((578939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c4 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-497341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1899011/2500000) (δ := 2957/250000000) (ψ := -136127/200000) 233 52
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t4 : ((-1243415248683/2500000000000 : ℚ) : ℝ) ≤ stT233 4 := by
  have hc : ((-248683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1243415248683/2500000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-248683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c5 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((256457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3278603/10000000) (δ := 11771/1000000000) (ψ := -136127/200000) 233 60
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t5 : ((229337343789/2000000000000 : ℚ) : ℝ) ≤ stT233 5 := by
  have hc : ((256407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229337343789/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((256407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c6 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-473221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -879009/1250000) (δ := 293/25000000) (ψ := -136127/200000) 233 67
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t6 : ((-966009374909/2500000000000 : ℚ) : ℝ) ≤ stT233 6 := by
  have hc : ((-236623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-966009374909/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-236623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c7 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-117291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 844179/2000000) (δ := 5909/500000000) (ψ := -136127/200000) 233 72
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t7 : ((-88701464789/2000000000000 : ℚ) : ℝ) ≤ stT233 7 := by
  have hc : ((-117341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88701464789/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-117341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c8 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((92243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3463119/10000000) (δ := 5877/500000000) (ψ := -136127/200000) 233 77
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t8 : ((163019891097/2500000000000 : ℚ) : ℝ) ≤ stT233 8 := by
  have hc : ((46109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163019891097/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((46109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c9 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-850241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64681/100000) (δ := 1169/100000000) (ψ := -136127/200000) 233 82
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t9 : ((-1417151950097/5000000000000 : ℚ) : ℝ) ≤ stT233 9 := by
  have hc : ((-850291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1417151950097/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-850291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c10 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-62473/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7780501/10000000) (δ := 11791/1000000000) (ψ := -136127/200000) 233 85
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t10 : ((-790267502451/2500000000000 : ℚ) : ℝ) ≤ stT233 10 := by
  have hc : ((-499809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-790267502451/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-499809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c11 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((196523/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11671/250000) (δ := 587/50000000) (ψ := -136127/200000) 233 89
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t11 : ((592508900969/2000000000000 : ℚ) : ℝ) ≤ stT233 11 := by
  have hc : ((196513/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((592508900969/2000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((196513/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c12 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-40029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 402709/1000000) (δ := 11841/1000000000) (ψ := -136127/200000) 233 92
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t12 : ((-3615566669/312500000000 : ℚ) : ℝ) ≤ stT233 12 := by
  have hc : ((-40079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3615566669/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-40079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c13 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((158891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3528073/10000000) (δ := 11819/1000000000) (ψ := -136127/200000) 233 95
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t13 : ((881091027/20000000000 : ℚ) : ℝ) ≤ stT233 13 := by
  have hc : ((158841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((881091027/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((158841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c14 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((985387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213953/5000000) (δ := 2361/200000000) (ψ := -136127/200000) 233 98
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t14 : ((658355872561/2500000000000 : ℚ) : ℝ) ≤ stT233 14 := by
  have hc : ((985337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((658355872561/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((985337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c15 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-980811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -920429/1250000) (δ := 2919/250000000) (ψ := -136127/200000) 233 101
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t15 : ((-2532572312529/10000000000000 : ℚ) : ℝ) ≤ stT233 15 := by
  have hc : ((-980861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2532572312529/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-980861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c16 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((7117/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -592841/5000000) (δ := 11741/1000000000) (ψ := -136127/200000) 233 103
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t16 : ((35583/160000 : ℚ) : ℝ) ≤ stT233 16 := by
  have hc : ((35583/40000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35583/160000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((35583/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c17 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((467011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2712221/10000000) (δ := 2351/200000000) (ψ := -136127/200000) 233 105
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t17 : ((283136665779/2500000000000 : ℚ) : ℝ) ≤ stT233 17 := by
  have hc : ((466961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((283136665779/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((466961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c18 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-65629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2295531/5000000) (δ := 11733/1000000000) (ψ := -136127/200000) 233 107
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t18 : ((-309437050509/5000000000000 : ℚ) : ℝ) ≤ stT233 18 := by
  have hc : ((-131283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309437050509/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-131283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c19 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-73143/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29183/62500) (δ := 1473/125000000) (ψ := -136127/200000) 233 109
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t19 : ((-167830275569/2500000000000 : ℚ) : ℝ) ≤ stT233 19 := by
  have hc : ((-146311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167830275569/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-146311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c20 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((156389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31317/100000) (δ := 2361/200000000) (ψ := -136127/200000) 233 111
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t20 : ((87410095097/1250000000000 : ℚ) : ℝ) ≤ stT233 20 := by
  have hc : ((39091/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87410095097/1250000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((39091/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c21 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((998519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27213/2000000) (δ := 1179/100000000) (ψ := -136127/200000) 233 113
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t21 : ((1089418542741/5000000000000 : ℚ) : ℝ) ≤ stT233 21 := by
  have hc : ((998469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1089418542741/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((998469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c22 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-101811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4181961/10000000) (δ := 11727/1000000000) (ψ := -136127/200000) 233 115
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t22 : ((-27146058361/1250000000000 : ℚ) : ℝ) ≤ stT233 22 := by
  have hc : ((-101861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27146058361/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-101861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c23 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-738271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6003249/10000000) (δ := 11669/1000000000) (ψ := -136127/200000) 233 116
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t23 : ((-307901268309/2000000000000 : ℚ) : ℝ) ≤ stT233 23 := by
  have hc : ((-738321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307901268309/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-738321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c24 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((969237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62171/1000000) (δ := 11849/1000000000) (ψ := -136127/200000) 233 118
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t24 : ((1978344241067/10000000000000 : ℚ) : ℝ) ≤ stT233 24 := by
  have hc : ((969187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1978344241067/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((969187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c25 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-986917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7449141/10000000) (δ := 11747/1000000000) (ψ := -136127/200000) 233 119
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t25 : ((-1973934986967/10000000000000 : ℚ) : ℝ) ≤ stT233 25 := by
  have hc : ((-986967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1973934986967/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-986967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c26 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((901189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140091/1250000) (δ := 11833/1000000000) (ψ := -136127/200000) 233 121
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t26 : ((1767278662379/10000000000000 : ℚ) : ℝ) ≤ stT233 26 := by
  have hc : ((901139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1767278662379/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((901139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c27 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-4717/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2577517/5000000) (δ := 11677/1000000000) (ψ := -136127/200000) 233 122
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t27 : ((-3631533387/40000000000 : ℚ) : ℝ) ≤ stT233 27 := by
  have hc : ((-1887/4000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3631533387/40000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-1887/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c28 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-221923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5076707/10000000) (δ := 737/62500000) (ψ := -136127/200000) 233 124
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t28 : ((-104860608801/1250000000000 : ℚ) : ℝ) ≤ stT233 28 := by
  have hc : ((-55487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104860608801/1250000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-55487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c29 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((990549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85997/2500000) (δ := 11799/1000000000) (ψ := -136127/200000) 233 125
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t29 : ((1839310089547/10000000000000 : ℚ) : ℝ) ≤ stT233 29 := by
  have hc : ((990499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1839310089547/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((990499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c30 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((23099/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461959/1250000) (δ := 11697/1000000000) (ψ := -136127/200000) 233 126
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t30 : ((84299939193/5000000000000 : ℚ) : ℝ) ≤ stT233 30 := by
  have hc : ((46173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84299939193/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((46173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c31 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-953407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3543913/5000000) (δ := 11813/1000000000) (ψ := -136127/200000) 233 127
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t31 : ((-856230129339/5000000000000 : ℚ) : ℝ) ≤ stT233 31 := by
  have hc : ((-953457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-856230129339/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-953457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c32 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-691091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5834483/10000000) (δ := 733/62500000) (ψ := -136127/200000) 233 129
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t32 : ((-1221776252147/10000000000000 : ℚ) : ℝ) ≤ stT233 32 := by
  have hc : ((-691141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1221776252147/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-691141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c33 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((61643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3617989/10000000) (δ := 2367/200000000) (ψ := -136127/200000) 233 130
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t33 : ((6703945973/312500000000 : ℚ) : ℝ) ≤ stT233 33 := by
  have hc : ((30809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6703945973/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((30809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c34 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((357339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96829/500000) (δ := 5871/500000000) (ψ := -136127/200000) 233 131
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t34 : ((61278815029/500000000000 : ℚ) : ℝ) ≤ stT233 34 := by
  have hc : ((178657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61278815029/500000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((178657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c35 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((238557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30373/400000) (δ := 5877/500000000) (ψ := -136127/200000) 233 132
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t35 : ((201606838353/1250000000000 : ℚ) : ℝ) ≤ stT233 35 := by
  have hc : ((477089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201606838353/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((477089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c36 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((999733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57739/10000000) (δ := 11747/1000000000) (ψ := -136127/200000) 233 133
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t36 : ((833068833439/5000000000000 : ℚ) : ℝ) ≤ stT233 36 := by
  have hc : ((999683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((833068833439/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((999683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c37 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((124623/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38843/2000000) (δ := 11839/1000000000) (ψ := -136127/200000) 233 134
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t37 : ((819474264863/5000000000000 : ℚ) : ℝ) ≤ stT233 37 := by
  have hc : ((498467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((819474264863/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((498467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c38 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((499983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20479/10000000) (δ := 11771/1000000000) (ψ := -136127/200000) 233 135
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t38 : ((202759716753/1250000000000 : ℚ) : ℝ) ≤ stT233 38 := by
  have hc : ((249979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202759716753/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((249979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c39 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((121913/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139189/2500000) (δ := 469/40000000) (ψ := -136127/200000) 233 136
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t39 : ((780827850187/5000000000000 : ℚ) : ℝ) ≤ stT233 39 := by
  have hc : ((487627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((780827850187/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((487627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c40 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((410727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1517101/10000000) (δ := 5909/500000000) (ψ := -136127/200000) 233 137
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t40 : ((162344134719/1250000000000 : ℚ) : ℝ) ≤ stT233 40 := by
  have hc : ((205351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162344134719/1250000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((205351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c41 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((105159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -355203/1250000) (δ := 737/62500000) (ψ := -136127/200000) 233 138
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t41 : ((328422358941/5000000000000 : ℚ) : ℝ) ≤ stT233 41 := by
  have hc : ((210293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328422358941/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((210293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c42 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-1451/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141023/312500) (δ := 2951/250000000) (ψ := -136127/200000) 233 139
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t42 : ((-17915396257/500000000000 : ℚ) : ℝ) ≤ stT233 42 := by
  have hc : ((-23221/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17915396257/500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-23221/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c43 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-859799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6514183/10000000) (δ := 2949/250000000) (ψ := -136127/200000) 233 140
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t43 : ((-655628843557/5000000000000 : ℚ) : ℝ) ≤ stT233 43 := by
  have hc : ((-859849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-655628843557/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-859849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c44 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-462319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6877201/10000000) (δ := 731/62500000) (ψ := -136127/200000) 233 140
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t44 : ((-87126241701/625000000000 : ℚ) : ℝ) ≤ stT233 44 := by
  have hc : ((-57793/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87126241701/625000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-57793/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c45 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-132669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1064911/2500000) (δ := 5857/500000000) (ψ := -136127/200000) 233 141
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t45 : ((-24730725741/1250000000000 : ℚ) : ℝ) ≤ stT233 45 := by
  have hc : ((-132719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24730725741/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-132719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c46 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((171361/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135439/1000000) (δ := 11721/1000000000) (ψ := -136127/200000) 233 142
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t46 : ((252643170069/2000000000000 : ℚ) : ℝ) ≤ stT233 46 := by
  have hc : ((171351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252643170069/2000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((171351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c47 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((372433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -913077/5000000) (δ := 471/40000000) (ψ := -136127/200000) 233 143
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t47 : ((67901569599/625000000000 : ℚ) : ℝ) ≤ stT233 47 := by
  have hc : ((46551/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67901569599/625000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((46551/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c48 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-511911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5270511/10000000) (δ := 2367/200000000) (ψ := -136127/200000) 233 144
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t48 : ((-46184513771/625000000000 : ℚ) : ℝ) ≤ stT233 48 := by
  have hc : ((-511961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46184513771/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-511961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c49 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-180477/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6740173/10000000) (δ := 2367/200000000) (ψ := -136127/200000) 233 144
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t49 : ((-64459668641/500000000000 : ℚ) : ℝ) ≤ stT233 49 := by
  have hc : ((-180487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64459668641/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-180487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c50 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((10889/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140017/500000) (δ := 147/12500000) (ψ := -136127/200000) 233 145
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t50 : ((61590390363/1000000000000 : ℚ) : ℝ) ≤ stT233 50 := by
  have hc : ((43551/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61590390363/1000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((43551/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c51 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((26657/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21447/156250) (δ := 237/20000000) (ψ := -136127/200000) 233 146
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t51 : ((14930030409/125000000000 : ℚ) : ℝ) ≤ stT233 51 := by
  have hc : ((426487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14930030409/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((426487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c52 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-672081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5769529/10000000) (δ := 5923/500000000) (ψ := -136127/200000) 233 147
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t52 : ((-932078336381/10000000000000 : ℚ) : ℝ) ≤ stT233 52 := by
  have hc : ((-672131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-932078336381/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-672131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c53 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-530867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166439/312500) (δ := 11657/1000000000) (ψ := -136127/200000) 233 147
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t53 : ((-364635388351/5000000000000 : ℚ) : ℝ) ≤ stT233 53 := by
  have hc : ((-530917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364635388351/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-530917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c54 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((61223/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 506233/10000000) (δ := 729/62500000) (ψ := -136127/200000) 233 148
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t54 : ((666477270693/5000000000000 : ℚ) : ℝ) ≤ stT233 54 := by
  have hc : ((489759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((666477270693/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((489759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c55 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-232411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225669/500000) (δ := 1479/125000000) (ψ := -136127/200000) 233 149
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t55 : ((-783626031/25000000000 : ℚ) : ℝ) ≤ stT233 55 := by
  have hc : ((-232461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-783626031/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-232461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c56 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-732619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5982397/10000000) (δ := 11771/1000000000) (ψ := -136127/200000) 233 149
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t56 : ((-979070713383/10000000000000 : ℚ) : ℝ) ≤ stT233 56 := by
  have hc : ((-732669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-979070713383/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-732669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c57 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((486399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11689/200000) (δ := 473/40000000) (ψ := -136127/200000) 233 150
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t57 : ((80527240871/625000000000 : ℚ) : ℝ) ≤ stT233 57 := by
  have hc : ((243187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80527240871/625000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((243187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c58 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-206761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4992789/10000000) (δ := 5893/500000000) (ψ := -136127/200000) 233 151
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t58 : ((-27152345909/500000000000 : ℚ) : ℝ) ≤ stT233 58 := by
  have hc : ((-103393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27152345909/500000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-103393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c59 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-201633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4964699/10000000) (δ := 5893/500000000) (ψ := -136127/200000) 233 151
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t59 : ((-13126826681/250000000000 : ℚ) : ℝ) ≤ stT233 59 := by
  have hc : ((-100829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13126826681/250000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-100829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c60 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((4641/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -953129/10000000) (δ := 1171/100000000) (ψ := -136127/200000) 233 152
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t60 : ((11982360811/100000000000 : ℚ) : ℝ) ≤ stT233 60 := by
  have hc : ((18563/20000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11982360811/100000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((18563/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c61 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-946533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281311/400000) (δ := 11703/1000000000) (ψ := -136127/200000) 233 153
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t61 : ((-1211975529127/10000000000000 : ℚ) : ℝ) ≤ stT233 61 := by
  have hc : ((-946583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1211975529127/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-946583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c62 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((560683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1219483/5000000) (δ := 11803/1000000000) (ψ := -136127/200000) 233 153
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t62 : ((712004470633/10000000000000 : ℚ) : ℝ) ≤ stT233 62 := by
  have hc : ((560633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((712004470633/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((560633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c63 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-8709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -987191/2500000) (δ := 731/62500000) (ψ := -136127/200000) 233 154
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t63 : ((-5517653219/5000000000000 : ℚ) : ℝ) ≤ stT233 63 := by
  have hc : ((-8759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5517653219/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-8759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c64 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-496057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5224621/10000000) (δ := 11707/1000000000) (ψ := -136127/200000) 233 154
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t64 : ((-620134246107/10000000000000 : ℚ) : ℝ) ≤ stT233 64 := by
  have hc : ((-496107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-620134246107/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-496107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c65 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((104499/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726073/5000000) (δ := 11689/1000000000) (ψ := -136127/200000) 233 155
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t65 : ((518429075937/5000000000000 : ℚ) : ℝ) ≤ stT233 65 := by
  have hc : ((417971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518429075937/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((417971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c66 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-493199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7441173/10000000) (δ := 5857/500000000) (ψ := -136127/200000) 233 155
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t66 : ((-15177920499/125000000000 : ℚ) : ℝ) ≤ stT233 66 := by
  have hc : ((-61653/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15177920499/125000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-61653/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c67 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((245159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246393/5000000) (δ := 11781/1000000000) (ψ := -136127/200000) 233 156
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t67 : ((299494008171/2500000000000 : ℚ) : ℝ) ≤ stT233 67 := by
  have hc : ((490293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299494008171/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((490293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c68 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-873991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6585381/10000000) (δ := 11729/1000000000) (ψ := -136127/200000) 233 157
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t68 : ((-1059931165839/10000000000000 : ℚ) : ℝ) ≤ stT233 68 := by
  have hc : ((-874041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1059931165839/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-874041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c69 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((35987/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95921/500000) (δ := 11729/1000000000) (ψ := -136127/200000) 233 157
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t69 : ((43320228201/500000000000 : ℚ) : ℝ) ≤ stT233 69 := by
  have hc : ((71969/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43320228201/500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((71969/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c70 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-558399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2704063/5000000) (δ := 11767/1000000000) (ψ := -136127/200000) 233 158
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t70 : ((-667474439821/10000000000000 : ℚ) : ℝ) ≤ stT233 70 := by
  have hc : ((-558449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-667474439821/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-558449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c71 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((415993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 713601/2500000) (δ := 1467/125000000) (ψ := -136127/200000) 233 158
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t71 : ((493633249483/10000000000000 : ℚ) : ℝ) ≤ stT233 71 := by
  have hc : ((415943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493633249483/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((415943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c72 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-306791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235327/500000) (δ := 147/12500000) (ψ := -136127/200000) 233 159
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t72 : ((-22600987537/625000000000 : ℚ) : ℝ) ≤ stT233 72 := by
  have hc : ((-306841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22600987537/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-306841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c73 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((29661/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1664029/5000000) (δ := 11843/1000000000) (ψ := -136127/200000) 233 159
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t73 : ((138832982409/5000000000000 : ℚ) : ℝ) ≤ stT233 73 := by
  have hc : ((118619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138832982409/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((118619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c74 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-104749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113661/2500000) (δ := 11753/1000000000) (ψ := -136127/200000) 233 160
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t74 : ((-60898682599/2500000000000 : ℚ) : ℝ) ≤ stT233 74 := by
  have hc : ((-52387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60898682599/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-52387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c75 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((27897/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420539/1250000) (δ := 11653/1000000000) (ψ := -136127/200000) 233 160
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t75 : ((1288217961/50000000000 : ℚ) : ℝ) ≤ stT233 75 := by
  have hc : ((111563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1288217961/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((111563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c76 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-276867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2314161/5000000) (δ := 11757/1000000000) (ψ := -136127/200000) 233 161
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t76 : ((-317645675443/10000000000000 : ℚ) : ℝ) ≤ stT233 76 := by
  have hc : ((-276917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-317645675443/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-276917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c77 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((183753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46659/156250) (δ := 11657/1000000000) (ψ := -136127/200000) 233 161
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t77 : ((2617216843/62500000000 : ℚ) : ℝ) ≤ stT233 77 := by
  have hc : ((11483/31250 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2617216843/62500000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((11483/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c78 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-244711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5205557/10000000) (δ := 5869/500000000) (ψ := -136127/200000) 233 162
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t78 : ((-135307221/2441406250 : ℚ) : ℝ) ≤ stT233 78 := by
  have hc : ((-7648/15625 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135307221/2441406250 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-7648/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c79 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((632543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2214911/10000000) (δ := 2353/200000000) (ψ := -136127/200000) 233 162
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t79 : ((711609651891/10000000000000 : ℚ) : ℝ) ≤ stT233 79 := by
  have hc : ((632493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((711609651891/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((632493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c80 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-390281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3082951/5000000) (δ := 11831/1000000000) (ψ := -136127/200000) 233 163
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t80 : ((-109093844601/1250000000000 : ℚ) : ℝ) ≤ stT233 80 := by
  have hc : ((-195153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109093844601/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-195153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c81 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((227441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214041/2000000) (δ := 2943/250000000) (ψ := -136127/200000) 233 163
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t81 : ((505396616127/5000000000000 : ℚ) : ℝ) ≤ stT233 81 := by
  have hc : ((454857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((505396616127/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((454857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c82 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-197889/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -299617/400000) (δ := 11779/1000000000) (ψ := -136127/200000) 233 164
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t82 : ((-54635758021/500000000000 : ℚ) : ℝ) ≤ stT233 82 := by
  have hc : ((-197899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54635758021/500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-197899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c83 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((61579/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42971/1000000) (δ := 2931/250000000) (ψ := -136127/200000) 233 164
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t83 : ((270353066347/2500000000000 : ℚ) : ℝ) ≤ stT233 83 := by
  have hc : ((492607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270353066347/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((492607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c84 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-216577/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3273199/5000000) (δ := 23479/1000000000) (ψ := -136127/200000) 233 164
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t84 : ((-47263727511/500000000000 : ℚ) : ℝ) ≤ stT233 84 := by
  have hc : ((-433179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47263727511/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-433179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c85 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((307977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2267999/10000000) (δ := 11817/1000000000) (ψ := -136127/200000) 233 165
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t85 : ((5219074261/78125000000 : ℚ) : ℝ) ≤ stT233 85 := by
  have hc : ((19247/31250 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5219074261/78125000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((19247/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c86 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-244663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4544921/10000000) (δ := 11817/1000000000) (ψ := -136127/200000) 233 165
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t86 : ((-32985109983/1250000000000 : ℚ) : ℝ) ≤ stT233 86 := by
  have hc : ((-244713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32985109983/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-244713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c87 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-99693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2214409/5000000) (δ := 1181/100000000) (ψ := -136127/200000) 233 166
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t87 : ((-53454482067/2500000000000 : ℚ) : ℝ) ≤ stT233 87 := by
  have hc : ((-49859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53454482067/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-49859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c88 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((125671/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5571/25000) (δ := 1171/100000000) (ψ := -136127/200000) 233 166
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t88 : ((133955002983/2000000000000 : ℚ) : ℝ) ≤ stT233 88 := by
  have hc : ((125661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133955002983/2000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((125661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c89 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-185543/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1724401/2500000) (δ := 59/5000000) (ψ := -136127/200000) 233 167
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t89 : ((-98342904447/1000000000000 : ℚ) : ℝ) ≤ stT233 89 := by
  have hc : ((-185553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98342904447/1000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-185553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c90 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((987909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -389157/10000000) (δ := 117/10000000) (ψ := -136127/200000) 233 167
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t90 : ((260323567257/2500000000000 : ℚ) : ℝ) ≤ stT233 90 := by
  have hc : ((987859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260323567257/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((987859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c91 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-375031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6047381/10000000) (δ := 47/2000000) (ψ := -136127/200000) 233 167
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t91 : ((-4914569737/62500000000 : ℚ) : ℝ) ≤ stT233 91 := by
  have hc : ((-23441/31250 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4914569737/62500000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-23441/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c92 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((12517/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3294411/10000000) (δ := 2927/250000000) (ψ := -136127/200000) 233 168
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t92 : ((6523633647/250000000000 : ℚ) : ℝ) ≤ stT233 92 := by
  have hc : ((25029/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6523633647/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((25029/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c93 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((180631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1501469/5000000) (δ := 2339/200000000) (ψ := -136127/200000) 233 168
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t93 : ((93639786153/2500000000000 : ℚ) : ℝ) ≤ stT233 93 := by
  have hc : ((90303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93639786153/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((90303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c94 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-425847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6475013/10000000) (δ := 1461/125000000) (ψ := -136127/200000) 233 169
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t94 : ((-13726679687/156250000000 : ℚ) : ℝ) ≤ stT233 94 := by
  have hc : ((-26617/31250 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13726679687/156250000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-26617/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c95 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((39691/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15547/500000) (δ := 2947/250000000) (ψ := -136127/200000) 233 169
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t95 : ((20360020421/200000000000 : ℚ) : ℝ) ≤ stT233 95 := by
  have hc : ((39689/40000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20360020421/200000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((39689/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c96 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-169427/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5788593/10000000) (δ := 2363/200000000) (ψ := -136127/200000) 233 169
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t96 : ((-345867023859/5000000000000 : ℚ) : ℝ) ≤ stT233 96 := by
  have hc : ((-338879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345867023859/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-338879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c97 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((17579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24269/62500) (δ := 11781/1000000000) (ψ := -136127/200000) 233 170
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t97 : ((8899000017/5000000000000 : ℚ) : ℝ) ≤ stT233 97 := by
  have hc : ((17529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8899000017/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((17529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c98 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((670029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 522843/2500000) (δ := 5911/500000000) (ψ := -136127/200000) 233 170
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t98 : ((84597578351/1250000000000 : ℚ) : ℝ) ≤ stT233 98 := by
  have hc : ((669979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84597578351/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((669979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c99 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-998173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7702819/10000000) (δ := 5887/500000000) (ψ := -136127/200000) 233 171
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t99 : ((-501626023737/5000000000000 : ℚ) : ℝ) ≤ stT233 99 := by
  have hc : ((-998223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501626023737/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-998223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c100 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((184717/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1848519/10000000) (δ := 5837/500000000) (ψ := -136127/200000) 233 171
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t100 : ((369408630591/5000000000000 : ℚ) : ℝ) ≤ stT233 100 := by
  have hc : ((369409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369408630591/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((369409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c101 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-8239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3947589/10000000) (δ := 5837/500000000) (ψ := -136127/200000) 233 171
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t101 : ((-4123934991/5000000000000 : ℚ) : ℝ) ≤ stT233 101 := by
  have hc : ((-8289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4123934991/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-8289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c102 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-743151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6021409/10000000) (δ := 2959/250000000) (ψ := -136127/200000) 233 172
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t102 : ((-183969745937/2500000000000 : ℚ) : ℝ) ≤ stT233 102 := by
  have hc : ((-743201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183969745937/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-743201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c103 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((15482/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338481/10000000) (δ := 1467/125000000) (ψ := -136127/200000) 233 172
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t103 : ((488131001271/5000000000000 : ℚ) : ℝ) ≤ stT233 103 := by
  have hc : ((495399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488131001271/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((495399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c104 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-518447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 661197/1250000) (δ := 2959/250000000) (ψ := -136127/200000) 233 172
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t104 : ((-508428306757/10000000000000 : ℚ) : ℝ) ≤ stT233 104 := by
  have hc : ((-518497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508428306757/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-518497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c105 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-358691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2422077/5000000) (δ := 11659/1000000000) (ψ := -136127/200000) 233 173
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t105 : ((-350095700641/10000000000000 : ℚ) : ℝ) ≤ stT233 105 := by
  have hc : ((-358741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350095700641/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-358741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c106 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((963537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677189/10000000) (δ := 367/31250000) (ψ := -136127/200000) 233 173
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t106 : ((187164094159/2000000000000 : ℚ) : ℝ) ≤ stT233 106 := by
  have hc : ((963487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187164094159/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((963487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c107 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-3103/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6146747/10000000) (δ := 11759/1000000000) (ψ := -136127/200000) 233 173
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t107 : ((-3749972823/50000000000 : ℚ) : ℝ) ≤ stT233 107 := by
  have hc : ((-3879/5000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3749972823/50000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-3879/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c108 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-21531/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -517821/1250000) (δ := 2913/250000000) (ψ := -136127/200000) 233 174
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t108 : ((-41460508837/5000000000000 : ℚ) : ℝ) ≤ stT233 108 := by
  have hc : ((-43087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41460508837/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-43087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c109 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((7057/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 613051/5000000) (δ := 11851/1000000000) (ψ := -136127/200000) 233 174
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t109 : ((16897487379/200000000000 : ℚ) : ℝ) ≤ stT233 109 := by
  have hc : ((35283/40000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16897487379/200000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((35283/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c110 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-173237/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6545783/10000000) (δ := 11751/1000000000) (ψ := -136127/200000) 233 174
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t110 : ((-165184604361/2000000000000 : ℚ) : ℝ) ≤ stT233 110 := by
  have hc : ((-173247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165184604361/2000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-173247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c111 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((291/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1945307/5000000) (δ := 2349/200000000) (ψ := -136127/200000) 233 175
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t111 : ((27525553/20000000000 : ℚ) : ℝ) ≤ stT233 111 := by
  have hc : ((29/2000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27525553/20000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((29/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c112 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((107633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 333399/2500000) (δ := 5879/500000000) (ψ := -136127/200000) 233 175
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t112 : ((406790799877/5000000000000 : ℚ) : ℝ) ≤ stT233 112 := by
  have hc : ((430507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((406790799877/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((430507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c113 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-429619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3255719/5000000) (δ := 2349/200000000) (ψ := -136127/200000) 233 175
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t113 : ((-101043783331/1250000000000 : ℚ) : ℝ) ≤ stT233 113 := by
  have hc : ((-107411/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101043783331/1250000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-107411/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c114 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-13729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4064351/10000000) (δ := 5919/500000000) (ψ := -136127/200000) 233 176
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t114 : ((-12870096519/2500000000000 : ℚ) : ℝ) ≤ stT233 114 := by
  have hc : ((-27483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12870096519/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-27483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c115 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((183487/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102303/1000000) (δ := 2353/200000000) (ψ := -136127/200000) 233 176
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t115 : ((21386629551/250000000000 : ℚ) : ℝ) ≤ stT233 115 := by
  have hc : ((183477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21386629551/250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((183477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c116 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-15101/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1213263/2000000) (δ := 2353/200000000) (ψ := -136127/200000) 233 176
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t116 : ((-7010929827/100000000000 : ℚ) : ℝ) ≤ stT233 116 := by
  have hc : ((-7551/10000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7010929827/100000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-7551/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c117 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-281961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -928317/2000000) (δ := 1459/125000000) (ψ := -136127/200000) 233 177
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t117 : ((-260719451511/10000000000000 : ℚ) : ℝ) ≤ stT233 117 := by
  have hc : ((-282011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260719451511/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-282011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c118 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((992027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157949/5000000) (δ := 2943/250000000) (ψ := -136127/200000) 233 177
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t118 : ((456594117399/5000000000000 : ℚ) : ℝ) ≤ stT233 118 := by
  have hc : ((991977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((456594117399/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((991977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c119 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-124611/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5231499/10000000) (δ := 2943/250000000) (ψ := -136127/200000) 233 177
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t119 : ((-228484475653/5000000000000 : ℚ) : ℝ) ≤ stT233 119 := by
  have hc : ((-249247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228484475653/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-249247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c120 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-620967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -560193/1000000) (δ := 2931/250000000) (ψ := -136127/200000) 233 178
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t120 : ((-566908409807/10000000000000 : ℚ) : ℝ) ≤ stT233 120 := by
  have hc : ((-621017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-566908409807/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-621017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c121 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((953199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -767879/10000000) (δ := 2931/250000000) (ψ := -136127/200000) 233 178
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t121 : ((86649822441/1000000000000 : ℚ) : ℝ) ≤ stT233 121 := by
  have hc : ((953149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86649822441/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((953149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c122 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-9937/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4026387/10000000) (δ := 739/62500000) (ψ := -136127/200000) 233 178
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t122 : ((-9007859421/2500000000000 : ℚ) : ℝ) ≤ stT233 122 := by
  have hc : ((-19899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9007859421/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-19899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c123 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-931961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3463227/5000000) (δ := 1477/125000000) (ψ := -136127/200000) 233 179
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t123 : ((-84036635837/1000000000000 : ℚ) : ℝ) ≤ stT233 123 := by
  have hc : ((-932011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84036635837/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-932011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c124 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((317057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -441967/2000000) (δ := 1477/125000000) (ψ := -136127/200000) 233 179
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t124 : ((17793936177/312500000000 : ℚ) : ℝ) ≤ stT233 124 := by
  have hc : ((39629/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17793936177/312500000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((39629/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c125 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((550721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1234461/5000000) (δ := 11687/1000000000) (ψ := -136127/200000) 233 179
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t125 : ((492535010517/10000000000000 : ℚ) : ℝ) ≤ stT233 125 := by
  have hc : ((550671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((492535010517/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((550671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c126 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-239023/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3555199/5000000) (δ := 1477/125000000) (ψ := -136127/200000) 233 179
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t126 : ((-425899589841/5000000000000 : ℚ) : ℝ) ≤ stT233 126 := by
  have hc : ((-478071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425899589841/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-478071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c127 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-13169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -998211/2500000) (δ := 5847/500000000) (ψ := -136127/200000) 233 180
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t127 : ((-5853894129/2500000000000 : ℚ) : ℝ) ≤ stT233 127 := by
  have hc : ((-6597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5853894129/2500000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-6597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c128 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((121699/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28791/500000) (δ := 5847/500000000) (ψ := -136127/200000) 233 180
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t128 : ((430248611793/5000000000000 : ℚ) : ℝ) ≤ stT233 128 := by
  have hc : ((486771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430248611793/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((486771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c129 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-455367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5108951/10000000) (δ := 11809/1000000000) (ψ := -136127/200000) 233 180
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t129 : ((-400972353067/10000000000000 : ℚ) : ℝ) ≤ stT233 129 := by
  have hc : ((-455417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400972353067/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-455417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c130 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-38203/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6100947/10000000) (δ := 5851/500000000) (ψ := -136127/200000) 233 181
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t130 : ((-67016955249/1000000000000 : ℚ) : ℝ) ≤ stT233 130 := by
  have hc : ((-76411/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67016955249/1000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-76411/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c131 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((158619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409327/2500000) (δ := 5901/500000000) (ψ := -136127/200000) 233 181
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t131 : ((17322164717/250000000000 : ℚ) : ℝ) ≤ stT233 131 := by
  have hc : ((158609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17322164717/250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((158609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c132 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((438427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 698093/2500000) (δ := 11701/1000000000) (ψ := -136127/200000) 233 181
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t132 : ((95389520069/2500000000000 : ℚ) : ℝ) ≤ stT233 132 := by
  have hc : ((438377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95389520069/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((438377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c133 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-120599/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 898577/1250000) (δ := 11701/1000000000) (ψ := -136127/200000) 233 181
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t133 : ((-41831207331/500000000000 : ℚ) : ℝ) ≤ stT233 133 := by
  have hc : ((-482421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41831207331/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-482421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c134 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-91493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1039011/2500000) (δ := 4679/200000000) (ψ := -136127/200000) 233 182
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t134 : ((-79081159867/10000000000000 : ℚ) : ℝ) ≤ stT233 134 := by
  have hc : ((-91543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79081159867/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-91543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c135 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((249389/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34963/2000000) (δ := 369/31250000) (ψ := -136127/200000) 233 182
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t135 : ((214628877243/2500000000000 : ℚ) : ℝ) ≤ stT233 135 := by
  have hc : ((498753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214628877243/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((498753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c136 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-108477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4473723/10000000) (δ := 2927/250000000) (ψ := -136127/200000) 233 182
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t136 : ((-46519852743/2500000000000 : ℚ) : ℝ) ≤ stT233 136 := by
  have hc : ((-54251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46519852743/2500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-54251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c137 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-937689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6966787/10000000) (δ := 2343/200000000) (ψ := -136127/200000) 233 183
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t137 : ((-400582408281/5000000000000 : ℚ) : ℝ) ≤ stT233 137 := by
  have hc : ((-937739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400582408281/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-937739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c138 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((92111/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2730439/10000000) (δ := 2363/200000000) (ψ := -136127/200000) 233 183
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t138 : ((9800191107/250000000000 : ℚ) : ℝ) ≤ stT233 138 := by
  have hc : ((92101/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9800191107/250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((92101/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c139 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((166171/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295077/2000000) (δ := 2947/250000000) (ψ := -136127/200000) 233 183
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t139 : ((35233941567/500000000000 : ℚ) : ℝ) ≤ stT233 139 := by
  have hc : ((166161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35233941567/500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((166161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c140 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-636243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5651037/10000000) (δ := 2363/200000000) (ψ := -136127/200000) 233 183
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t140 : ((-107553242083/2000000000000 : ℚ) : ℝ) ≤ stT233 140 := by
  have hc : ((-636293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107553242083/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-636293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c141 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-712897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5911041/10000000) (δ := 11723/1000000000) (ψ := -136127/200000) 233 184
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t141 : ((-75051217743/1250000000000 : ℚ) : ℝ) ≤ stT233 141 := by
  have hc : ((-712947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75051217743/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-712947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c142 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((376641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1794397/10000000) (δ := 11723/1000000000) (ψ := -136127/200000) 233 184
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t142 : ((39506123937/625000000000 : ℚ) : ℝ) ≤ stT233 142 := by
  have hc : ((47077/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39506123937/625000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((47077/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c143 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((607933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 458671/2000000) (δ := 11723/1000000000) (ψ := -136127/200000) 233 184
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t143 : ((254168647843/5000000000000 : ℚ) : ℝ) ≤ stT233 143 := by
  have hc : ((607883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254168647843/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((607883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c144 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-165003/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1588141/2500000) (δ := 589/50000000) (ψ := -136127/200000) 233 184
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t144 : ((-68755471671/1000000000000 : ℚ) : ℝ) ≤ stT233 144 := by
  have hc : ((-165013/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68755471671/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-165013/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c145 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-530243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -332763/625000) (δ := 11773/1000000000) (ψ := -136127/200000) 233 185
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t145 : ((-88076894663/2000000000000 : ℚ) : ℝ) ≤ stT233 145 := by
  have hc : ((-530293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88076894663/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-530293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c146 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((863667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1320743/10000000) (δ := 1183/100000000) (ψ := -136127/200000) 233 185
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t146 : ((142946749457/2000000000000 : ℚ) : ℝ) ≤ stT233 146 := by
  have hc : ((863617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142946749457/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((863617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c147 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((487007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2655343/10000000) (δ := 11773/1000000000) (ψ := -136127/200000) 233 185
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t147 : ((200817658101/5000000000000 : ℚ) : ℝ) ≤ stT233 147 := by
  have hc : ((486957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200817658101/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((486957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c148 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-438843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6604519/10000000) (δ := 1183/100000000) (ψ := -136127/200000) 233 185
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t148 : ((-18037365083/250000000000 : ℚ) : ℝ) ≤ stT233 148 := by
  have hc : ((-109717/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18037365083/250000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-109717/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c149 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-480773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5180831/10000000) (δ := 11837/1000000000) (ψ := -136127/200000) 233 186
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t149 : ((-12309549623/312500000000 : ℚ) : ℝ) ≤ stT233 149 := by
  have hc : ((-480823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12309549623/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-480823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c150 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((435437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1284547/10000000) (δ := 11737/1000000000) (ψ := -136127/200000) 233 186
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t150 : ((5554877443/78125000000 : ℚ) : ℝ) ≤ stT233 150 := by
  have hc : ((108853/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5554877443/78125000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((108853/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c151 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((102213/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646483/2500000) (δ := 5883/500000000) (ψ := -136127/200000) 233 186
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t151 : ((20792893741/500000000000 : ℚ) : ℝ) ≤ stT233 151 := by
  have hc : ((102203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20792893741/500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((102203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c152 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-421151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160771/250000) (δ := 5833/500000000) (ψ := -136127/200000) 233 186
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t152 : ((-10675600719/156250000000 : ℚ) : ℝ) ≤ stT233 152 := by
  have hc : ((-52647/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10675600719/156250000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-52647/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c153 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-143663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2728719/5000000) (δ := 11759/1000000000) (ψ := -136127/200000) 233 187
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t153 : ((-232309778003/5000000000000 : ℚ) : ℝ) ≤ stT233 153 := by
  have hc : ((-287351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232309778003/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-287351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c154 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((393443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13301/80000) (δ := 11659/1000000000) (ψ := -136127/200000) 233 187
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t154 : ((79256219899/1250000000000 : ℚ) : ℝ) ≤ stT233 154 := by
  have hc : ((196709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79256219899/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((196709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c155 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((332597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1053803/5000000) (δ := 11759/1000000000) (ψ := -136127/200000) 233 187
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t155 : ((66782037317/1250000000000 : ℚ) : ℝ) ≤ stT233 155 := by
  have hc : ((83143/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66782037317/1250000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((83143/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c156 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-696599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2926803/5000000) (δ := 2961/250000000) (ψ := -136127/200000) 233 187
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t156 : ((-557765752009/10000000000000 : ℚ) : ℝ) ≤ stT233 156 := by
  have hc : ((-696649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557765752009/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-696649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c157 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-77209/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6132299/10000000) (δ := 11751/1000000000) (ψ := -136127/200000) 233 188
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t157 : ((-30811744809/500000000000 : ℚ) : ℝ) ≤ stT233 157 := by
  have hc : ((-38607/50000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30811744809/500000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-38607/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c158 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((562363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243389/1000000) (δ := 11751/1000000000) (ψ := -136127/200000) 233 188
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t158 : ((447352043341/10000000000000 : ℚ) : ℝ) ≤ stT233 158 := by
  have hc : ((562313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((447352043341/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((562313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c159 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((879261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1241219/10000000) (δ := 11751/1000000000) (ψ := -136127/200000) 233 188
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t159 : ((697259162761/10000000000000 : ℚ) : ℝ) ≤ stT233 159 := by
  have hc : ((879211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((697259162761/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((879211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c160 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-94239/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4893261/10000000) (δ := 11751/1000000000) (ψ := -136127/200000) 233 188
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t160 : ((-14902481671/500000000000 : ℚ) : ℝ) ≤ stT233 160 := by
  have hc : ((-188503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14902481671/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-188503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c161 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-120557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1796359/2500000) (δ := 5879/500000000) (ψ := -136127/200000) 233 189
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t161 : ((-380068894083/5000000000000 : ℚ) : ℝ) ≤ stT233 161 := by
  have hc : ((-482253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-380068894083/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-482253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c162 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((138907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -894649/2500000) (δ := 5879/500000000) (ψ := -136127/200000) 233 189
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t162 : ((54548167309/5000000000000 : ℚ) : ℝ) ≤ stT233 162 := by
  have hc : ((138857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54548167309/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((138857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c163 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((999997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121/200000) (δ := 2369/200000000) (ψ := -136127/200000) 233 189
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t163 : ((39160924361/500000000000 : ℚ) : ℝ) ≤ stT233 163 := by
  have hc : ((999947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39160924361/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((999947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c164 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((35703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3568737/10000000) (δ := 5829/500000000) (ψ := -136127/200000) 233 189
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t164 : ((13934784677/1250000000000 : ℚ) : ℝ) ≤ stT233 164 := by
  have hc : ((71381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13934784677/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((71381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c165 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-59751/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3554877/5000000) (δ := 2369/200000000) (ψ := -136127/200000) 233 189
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t165 : ((-372148212467/5000000000000 : ℚ) : ℝ) ≤ stT233 165 := by
  have hc : ((-478033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-372148212467/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-478033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c166 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-222257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5078569/10000000) (δ := 5833/500000000) (ψ := -136127/200000) 233 190
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t166 : ((-86262198291/2500000000000 : ℚ) : ℝ) ≤ stT233 166 := by
  have hc : ((-111141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86262198291/2500000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-111141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c167 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((201711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98751/625000) (δ := 11737/1000000000) (ψ := -136127/200000) 233 190
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t167 : ((312157876731/5000000000000 : ℚ) : ℝ) ≤ stT233 167 := by
  have hc : ((403397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312157876731/5000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((403397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c168 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((362753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1897567/10000000) (δ := 11837/1000000000) (ψ := -136127/200000) 233 190
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t168 : ((8745326739/156250000000 : ℚ) : ℝ) ≤ stT233 168 := by
  have hc : ((45341/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8745326739/156250000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((45341/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c169 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-270253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1338647/2500000) (δ := 11837/1000000000) (ψ := -136127/200000) 233 190
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t169 : ((-103953108109/2500000000000 : ℚ) : ℝ) ≤ stT233 169 := by
  have hc : ((-135139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103953108109/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-135139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c170 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-465277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4323/6250) (δ := 1183/100000000) (ψ := -136127/200000) 233 191
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t170 : ((-35687034843/500000000000 : ℚ) : ℝ) ≤ stT233 170 := by
  have hc : ((-232651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35687034843/500000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-232651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c171 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((84909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3500379/10000000) (δ := 1173/100000000) (ψ := -136127/200000) 233 191
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t171 : ((16228101899/1250000000000 : ℚ) : ℝ) ≤ stT233 171 := by
  have hc : ((21221/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16228101899/1250000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((21221/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c172 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((999137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2597/250000) (δ := 1183/100000000) (ψ := -136127/200000) 233 191
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t172 : ((190448961201/2500000000000 : ℚ) : ℝ) ≤ stT233 172 := by
  have hc : ((999087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190448961201/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((999087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c173 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((5173/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3272931/10000000) (δ := 1173/100000000) (ψ := -136127/200000) 233 191
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t173 : ((196609701/10000000000 : ℚ) : ℝ) ≤ stT233 173 := by
  have hc : ((1293/5000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196609701/10000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((1293/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c174 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-441289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3315143/5000000) (δ := 1183/100000000) (ψ := -136127/200000) 233 191
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t174 : ((-167279851043/2500000000000 : ℚ) : ℝ) ≤ stT233 174 := by
  have hc : ((-220657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167279851043/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-220657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c175 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-663151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -717443/1250000) (δ := 73/6250000) (ψ := -136127/200000) 233 192
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t175 : ((-501332868729/10000000000000 : ℚ) : ℝ) ≤ stT233 175 := by
  have hc : ((-663201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501332868729/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-663201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c176 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((566797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2420459/10000000) (δ := 73/6250000) (ψ := -136127/200000) 233 192
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t176 : ((213600710083/5000000000000 : ℚ) : ℝ) ≤ stT233 176 := by
  have hc : ((566747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213600710083/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((566747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c177 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((938703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879869/10000000) (δ := 11823/1000000000) (ψ := -136127/200000) 233 192
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t177 : ((352767386419/5000000000000 : ℚ) : ℝ) ≤ stT233 177 := by
  have hc : ((938653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352767386419/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((938653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c178 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-93689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2080779/5000000) (δ := 73/6250000) (ψ := -136127/200000) 233 192
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t178 : ((-17565095037/2500000000000 : ℚ) : ℝ) ≤ stT233 178 := by
  have hc : ((-93739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17565095037/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-93739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c179 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-985307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3712449/5000000) (δ := 589/50000000) (ψ := -136127/200000) 233 192
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t179 : ((-184122823663/2500000000000 : ℚ) : ℝ) ≤ stT233 179 := by
  have hc : ((-985357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184122823663/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-985357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c180 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-26869/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2518979/5000000) (δ := 11687/1000000000) (ψ := -136127/200000) 233 193
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t180 : ((-40058599203/1250000000000 : ℚ) : ℝ) ≤ stT233 180 := by
  have hc : ((-214977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40058599203/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-214977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c181 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((93619/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226349/1250000) (δ := 1477/125000000) (ψ := -136127/200000) 233 193
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t181 : ((139163590797/2500000000000 : ℚ) : ℝ) ≤ stT233 181 := by
  have hc : ((374451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139163590797/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((374451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c182 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((847563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27971/200000) (δ := 1477/125000000) (ψ := -136127/200000) 233 193
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t182 : ((628218163737/10000000000000 : ℚ) : ℝ) ≤ stT233 182 := by
  have hc : ((847513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((628218163737/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((847513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c183 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-65561/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4590359/10000000) (δ := 2929/250000000) (ψ := -136127/200000) 233 193
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t183 : ((-48473373817/2500000000000 : ℚ) : ℝ) ≤ stT233 183 := by
  have hc : ((-131147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48473373817/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-131147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c184 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-999363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7764751/10000000) (δ := 2929/250000000) (ψ := -136127/200000) 233 193
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t184 : ((-73677725773/1000000000000 : ℚ) : ℝ) ≤ stT233 184 := by
  have hc : ((-999413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73677725773/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-999413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c185 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-84221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1196501/2500000) (δ := 11709/1000000000) (ψ := -136127/200000) 233 194
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t185 : ((-24771893081/1000000000000 : ℚ) : ℝ) ≤ stT233 185 := by
  have hc : ((-168467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24771893081/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-168467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c186 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((395503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1645863/10000000) (δ := 11709/1000000000) (ψ := -136127/200000) 233 194
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t186 : ((28997831133/500000000000 : ℚ) : ℝ) ≤ stT233 186 := by
  have hc : ((197739/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28997831133/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((197739/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c187 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((830383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 738751/5000000) (δ := 11709/1000000000) (ψ := -136127/200000) 233 194
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t187 : ((75899909197/1250000000000 : ℚ) : ℝ) ≤ stT233 187 := by
  have hc : ((830333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75899909197/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((830333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c188 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-259847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4584149/10000000) (δ := 11809/1000000000) (ψ := -136127/200000) 233 194
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t188 : ((-7581975181/400000000000 : ℚ) : ℝ) ≤ stT233 188 := by
  have hc : ((-259897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7581975181/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-259897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c189 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-49871/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 767437/1000000) (δ := 11709/1000000000) (ψ := -136127/200000) 233 194
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t189 : ((-72555269571/1000000000000 : ℚ) : ℝ) ≤ stT233 189 := by
  have hc : ((-99747/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72555269571/1000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-99747/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c190 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-401451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4959741/10000000) (δ := 11801/1000000000) (ψ := -136127/200000) 233 195
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t190 : ((-291279740977/10000000000000 : ℚ) : ℝ) ≤ stT233 190 := by
  have hc : ((-401501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291279740977/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-401501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c191 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((362147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -380393/2000000) (δ := 5851/500000000) (ψ := -136127/200000) 233 195
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t191 : ((65505516007/1250000000000 : ℚ) : ℝ) ≤ stT233 191 := by
  have hc : ((181061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65505516007/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((181061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c192 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((448929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71237/625000) (δ := 5901/500000000) (ψ := -136127/200000) 233 195
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t192 : ((40496022631/625000000000 : ℚ) : ℝ) ≤ stT233 192 := by
  have hc : ((56113/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40496022631/625000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((56113/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c193 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-23841/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4165763/10000000) (δ := 5901/500000000) (ψ := -136127/200000) 233 195
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t193 : ((-4292532739/625000000000 : ℚ) : ℝ) ≤ stT233 193 := by
  have hc : ((-47707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4292532739/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-47707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c194 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-192693/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7176123/10000000) (δ := 5901/500000000) (ψ := -136127/200000) 233 195
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t194 : ((-138352853177/2000000000000 : ℚ) : ℝ) ≤ stT233 194 := by
  have hc : ((-192703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138352853177/2000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-192703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c195 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-300197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221479/400000) (δ := 11709/1000000000) (ψ := -136127/200000) 233 196
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t195 : ((-21499347753/500000000000 : ℚ) : ℝ) ≤ stT233 195 := by
  have hc : ((-150111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21499347753/500000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-150111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c196 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((8138/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2557429/10000000) (δ := 11809/1000000000) (ψ := -136127/200000) 233 196
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t196 : ((37198677087/1000000000000 : ℚ) : ℝ) ≤ stT233 196 := by
  have hc : ((260391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37198677087/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((260391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c197 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((986779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 406971/10000000) (δ := 5897/500000000) (ψ := -136127/200000) 233 196
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t197 : ((70301481063/1000000000000 : ℚ) : ℝ) ≤ stT233 197 := by
  have hc : ((986729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70301481063/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((986729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c198 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((113141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419543/1250000) (δ := 11809/1000000000) (ψ := -136127/200000) 233 196
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t198 : ((20097008651/1250000000000 : ℚ) : ℝ) ≤ stT233 198 := by
  have hc : ((28279/125000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20097008651/1250000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((28279/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c199 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-405409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3145431/5000000) (δ := 5847/500000000) (ψ := -136127/200000) 233 196
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t199 : ((-71851216197/1250000000000 : ℚ) : ℝ) ≤ stT233 199 := by
  have hc : ((-202717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71851216197/1250000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-202717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c200 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-53521/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162433/250000) (δ := 11687/1000000000) (ψ := -136127/200000) 233 197
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t200 : ((-302778267651/5000000000000 : ℚ) : ℝ) ≤ stT233 200 := by
  have hc : ((-428193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302778267651/5000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-428193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c201 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((133579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3592043/10000000) (δ := 11687/1000000000) (ψ := -136127/200000) 233 197
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t201 : ((18836802501/2000000000000 : ℚ) : ℝ) ≤ stT233 201 := by
  have hc : ((133529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18836802501/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((133529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c202 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((192183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70127/1000000) (δ := 2929/250000000) (ψ := -136127/200000) 233 197
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t202 : ((135212346281/2000000000000 : ℚ) : ℝ) ≤ stT233 202 := by
  have hc : ((192173/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135212346281/2000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((192173/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c203 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((322369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 217529/1000000) (δ := 1477/125000000) (ψ := -136127/200000) 233 197
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t203 : ((14140062783/312500000000 : ℚ) : ℝ) ≤ stT233 203 := by
  have hc : ((40293/62500 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14140062783/312500000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((40293/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c204 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-429809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1007539/2000000) (δ := 1477/125000000) (ψ := -136127/200000) 233 197
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t204 : ((-300961910119/10000000000000 : ℚ) : ℝ) ≤ stT233 204 := by
  have hc : ((-429859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300961910119/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-429859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c205 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-999917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1955461/2500000) (δ := 589/50000000) (ψ := -136127/200000) 233 198
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t205 : ((-698407951777/10000000000000 : ℚ) : ℝ) ≤ stT233 205 := by
  have hc : ((-999967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-698407951777/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-999967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c206 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-102879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2493641/5000000) (δ := 11723/1000000000) (ψ := -136127/200000) 233 198
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t206 : ((-71688006361/2500000000000 : ℚ) : ℝ) ≤ stT233 206 := by
  have hc : ((-205783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71688006361/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-205783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c207 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((647431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541617/2500000) (δ := 589/50000000) (ψ := -136127/200000) 233 198
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t207 : ((56245108661/1250000000000 : ℚ) : ℝ) ≤ stT233 207 := by
  have hc : ((647381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56245108661/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((647381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c208 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((241833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25631/400000) (δ := 11823/1000000000) (ψ := -136127/200000) 233 198
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t208 : ((2682756627/40000000000 : ℚ) : ℝ) ≤ stT233 208 := by
  have hc : ((483641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2682756627/40000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((483641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c209 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((195701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3434561/10000000) (δ := 73/6250000) (ψ := -136127/200000) 233 198
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t209 : ((67667267907/5000000000000 : ℚ) : ℝ) ≤ stT233 209 := by
  have hc : ((195651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67667267907/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((195651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c210 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-792689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194219/312500) (δ := 589/50000000) (ψ := -136127/200000) 233 198
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t210 : ((-273521115387/5000000000000 : ℚ) : ℝ) ≤ stT233 210 := by
  have hc : ((-792739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273521115387/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-792739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c211 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-899881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -672573/1000000) (δ := 1183/100000000) (ψ := -136127/200000) 233 199
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t211 : ((-619538598399/10000000000000 : ℚ) : ℝ) ≤ stT233 211 := by
  have hc : ((-899931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619538598399/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-899931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c212 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-2231/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -992903/2500000) (δ := 1173/100000000) (ψ := -136127/200000) 233 199
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t212 : ((-6146200047/5000000000000 : ℚ) : ℝ) ≤ stT233 212 := by
  have hc : ((-8949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6146200047/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-8949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c213 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((88131/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -49217/400000) (δ := 1183/100000000) (ψ := -136127/200000) 233 199
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t213 : ((7547859711/125000000000 : ℚ) : ℝ) ≤ stT233 213 := by
  have hc : ((44063/50000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7547859711/125000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((44063/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c214 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((825799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 748973/5000000) (δ := 11773/1000000000) (ψ := -136127/200000) 233 199
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t214 : ((112893926033/2000000000000 : ℚ) : ℝ) ≤ stT233 214 := by
  have hc : ((825749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112893926033/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((825749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c215 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-114377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4213561/10000000) (δ := 11773/1000000000) (ψ := -136127/200000) 233 199
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t215 : ((-15607728373/2000000000000 : ℚ) : ℝ) ≤ stT233 215 := by
  have hc : ((-114427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15607728373/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-114427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c216 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-232631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3458297/5000000) (δ := 11773/1000000000) (ψ := -136127/200000) 233 199
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t216 : ((-158293894409/2500000000000 : ℚ) : ℝ) ≤ stT233 216 := by
  have hc : ((-465287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158293894409/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-465287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c217 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-764037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305043/500000) (δ := 5883/500000000) (ψ := -136127/200000) 233 200
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t217 : ((-103739327903/2000000000000 : ℚ) : ℝ) ≤ stT233 217 := by
  have hc : ((-764087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103739327903/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-764087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c218 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((6261/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3422699/10000000) (δ := 11837/1000000000) (ψ := -136127/200000) 233 200
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t218 : ((13566154007/1000000000000 : ℚ) : ℝ) ≤ stT233 218 := by
  have hc : ((100151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13566154007/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((100151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c219 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((238633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189193/2500000) (δ := 5883/500000000) (ψ := -136127/200000) 233 200
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t219 : ((322489401617/5000000000000 : ℚ) : ℝ) ≤ stT233 219 := by
  have hc : ((477241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322489401617/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((477241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c220 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((725667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 948491/5000000) (δ := 11737/1000000000) (ψ := -136127/200000) 233 200
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t220 : ((489210255783/10000000000000 : ℚ) : ℝ) ≤ stT233 220 := by
  have hc : ((725617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489210255783/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((725617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c221 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-242263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 283671/625000) (δ := 11737/1000000000) (ψ := -136127/200000) 233 200
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t221 : ((-162997412649/10000000000000 : ℚ) : ℝ) ≤ stT233 221 := by
  have hc : ((-242313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162997412649/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-242313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c222 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-962643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 716849/1000000) (δ := 5883/500000000) (ψ := -136127/200000) 233 200
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t222 : ((-646118145801/10000000000000 : ℚ) : ℝ) ≤ stT233 222 := by
  have hc : ((-962693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-646118145801/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-962693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c223 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-35791/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1184297/2000000) (δ := 5829/500000000) (ψ := -136127/200000) 233 201
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t223 : ((-958764691/20000000000 : ℚ) : ℝ) ≤ stT233 223 := by
  have hc : ((-71587/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-958764691/20000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-71587/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c224 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((242279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -663041/2000000) (δ := 2349/200000000) (ψ := -136127/200000) 233 201
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t224 : ((161846033037/10000000000000 : ℚ) : ℝ) ≤ stT233 224 := by
  have hc : ((242229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161846033037/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((242229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c225 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((191751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -720517/10000000) (δ := 2349/200000000) (ψ := -136127/200000) 233 201
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t225 : ((63913602753/1000000000000 : ℚ) : ℝ) ≤ stT233 225 := by
  have hc : ((191741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63913602753/1000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((191741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c226 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((735059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116413/625000) (δ := 11679/500000000) (ψ := -136127/200000) 233 201
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t226 : ((48892063671/1000000000000 : ℚ) : ℝ) ≤ stT233 226 := by
  have hc : ((735009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48892063671/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((735009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c227 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-201563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1419/3200) (δ := 2349/200000000) (ψ := -136127/200000) 233 201
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t227 : ((-33453846703/2500000000000 : ℚ) : ℝ) ≤ stT233 227 := by
  have hc : ((-201613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33453846703/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-201613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c228 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-37661/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1748703/2500000) (δ := 2349/200000000) (ψ := -136127/200000) 233 201
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t228 : ((-24942962021/400000000000 : ℚ) : ℝ) ≤ stT233 228 := by
  have hc : ((-37663/40000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24942962021/400000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-37663/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c229 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-780061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6163899/10000000) (δ := 11851/1000000000) (ψ := -136127/200000) 233 202
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t229 : ((-515512170909/10000000000000 : ℚ) : ℝ) ≤ stT233 229 := by
  have hc : ((-780111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515512170909/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-780111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c230 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((120197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3625771/10000000) (δ := 1469/125000000) (ψ := -136127/200000) 233 202
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t230 : ((3961126443/500000000000 : ℚ) : ℝ) ≤ stT233 230 := by
  have hc : ((120147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3961126443/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((120147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c231 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((904981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1098653/10000000) (δ := 1469/125000000) (ψ := -136127/200000) 233 202
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t231 : ((595400256381/10000000000000 : ℚ) : ℝ) ≤ stT233 231 := by
  have hc : ((904931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((595400256381/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((904931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c232 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((843513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 708757/5000000) (δ := 1469/125000000) (ψ := -136127/200000) 233 202
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t232 : ((138440112579/2500000000000 : ℚ) : ℝ) ≤ stT233 232 := by
  have hc : ((843463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138440112579/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((843463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c233 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((327/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490363/1250000) (δ := 11851/1000000000) (ψ := -136127/200000) 233 202
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t233 : ((207673357/2000000000000 : ℚ) : ℝ) ≤ stT233 233 := by
  have hc : ((317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207673357/2000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c234 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-839431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6417577/10000000) (δ := 11751/1000000000) (ψ := -136127/200000) 233 202
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t234 : ((-548786358801/10000000000000 : ℚ) : ℝ) ≤ stT233 234 := by
  have hc : ((-839481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548786358801/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-839481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c235 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-913479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6806373/10000000) (δ := 11659/1000000000) (ψ := -136127/200000) 233 203
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t235 : ((-595921459041/10000000000000 : ℚ) : ℝ) ≤ stT233 235 := by
  have hc : ((-913529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-595921459041/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-913529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c236 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-40413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4332903/10000000) (δ := 11759/1000000000) (ψ := -136127/200000) 233 203
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t236 : ((-10525910839/1000000000000 : ℚ) : ℝ) ≤ stT233 236 := by
  have hc : ((-80851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10525910839/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-80851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c237 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((733073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1869919/10000000) (δ := 2961/250000000) (ψ := -136127/200000) 233 203
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t237 : ((476149017087/10000000000000 : ℚ) : ℝ) ≤ stT233 237 := by
  have hc : ((733023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476149017087/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((733023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c238 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((6081/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291349/5000000) (δ := 11759/1000000000) (ψ := -136127/200000) 233 203
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t238 : ((63064318073/1000000000000 : ℚ) : ℝ) ≤ stT233 238 := by
  have hc : ((97291/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63064318073/1000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((97291/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c239 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((88249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1512531/5000000) (δ := 11659/1000000000) (ψ := -136127/200000) 233 203
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t239 : ((57075427079/2500000000000 : ℚ) : ℝ) ≤ stT233 239 := by
  have hc : ((176473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57075427079/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((176473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c240 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-114917/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 341077/625000) (δ := 2961/250000000) (ψ := -136127/200000) 233 203
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t240 : ((-37092574323/1000000000000 : ℚ) : ℝ) ≤ stT233 240 := by
  have hc : ((-114927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37092574323/1000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-114927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c241 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-999949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -978587/1250000) (δ := 11737/1000000000) (ψ := -136127/200000) 233 204
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t241 : ((-644156355843/10000000000000 : ℚ) : ℝ) ≤ stT233 241 := by
  have hc : ((-999999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-644156355843/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-999999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c242 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-280617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135417/250000) (δ := 11737/1000000000) (ψ := -136127/200000) 233 204
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t242 : ((-3608073873/100000000000 : ℚ) : ℝ) ≤ stT233 242 := by
  have hc : ((-140321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3608073873/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-140321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c243 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((356899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24117/80000) (δ := 11837/1000000000) (ψ := -136127/200000) 233 204
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t243 : ((457837267/20000000000 : ℚ) : ℝ) ≤ stT233 243 := by
  have hc : ((356849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((457837267/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((356849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c244 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((60573/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311207/5000000) (δ := 11837/1000000000) (ψ := -136127/200000) 233 204
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t244 : ((38775864857/625000000000 : ℚ) : ℝ) ≤ stT233 244 := by
  have hc : ((484559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38775864857/625000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((484559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c245 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((95283/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879991/5000000) (δ := 23437/1000000000) (ψ := -136127/200000) 233 204
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t245 : ((60870028933/1250000000000 : ℚ) : ℝ) ≤ stT233 245 := by
  have hc : ((381107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60870028933/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((381107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c246 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-41097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4132709/10000000) (δ := 5883/500000000) (ψ := -136127/200000) 233 204
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t246 : ((-13109220697/2500000000000 : ℚ) : ℝ) ≤ stT233 246 := by
  have hc : ((-20561/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13109220697/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-20561/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c247 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-42801/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1299159/2000000) (δ := 5883/500000000) (ψ := -136127/200000) 233 204
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t247 : ((-10894089999/200000000000 : ℚ) : ℝ) ≤ stT233 247 := by
  have hc : ((-85607/100000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10894089999/200000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-85607/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c248 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-115223/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1714659/2500000) (δ := 1183/100000000) (ψ := -136127/200000) 233 205
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t248 : ((-292682755917/5000000000000 : ℚ) : ℝ) ≤ stT233 248 := by
  have hc : ((-460917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292682755917/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-460917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c249 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-58221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4514597/10000000) (δ := 11773/1000000000) (ψ := -136127/200000) 233 205
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t249 : ((-2952321983/200000000000 : ℚ) : ℝ) ≤ stT233 249 := by
  have hc : ((-116467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2952321983/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-116467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_c250 :
    |Real.cos (((233 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((321667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2179879/10000000) (δ := 11673/1000000000) (ψ := -136127/200000) 233 205
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st233_t250 : ((20342409111/500000000000 : ℚ) : ℝ) ≤ stT233 250 := by
  have hc : ((160821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((233 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st233_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20342409111/500000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((160821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st233_p1 : ((777123/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT233 (i+1) := by
  rw [Finset.sum_range_one]
  exact st233_t1

theorem st233_p2 : ((5235814030449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT233 (i+1))
      = (∑ i ∈ Finset.range 1, stT233 (i+1)) + stT233 2 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 1
    simpa using h
  have hprev := st233_p1
  have hstep := st233_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p3 : ((3453533383819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT233 (i+1))
      = (∑ i ∈ Finset.range 2, stT233 (i+1)) + stT233 3 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 2
    simpa using h
  have hprev := st233_p2
  have hstep := st233_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p4 : ((69066191723/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT233 (i+1))
      = (∑ i ∈ Finset.range 3, stT233 (i+1)) + stT233 4 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 3
    simpa using h
  have hprev := st233_p3
  have hstep := st233_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p5 : ((9987159259489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT233 (i+1))
      = (∑ i ∈ Finset.range 4, stT233 (i+1)) + stT233 5 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 4
    simpa using h
  have hprev := st233_p4
  have hstep := st233_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p6 : ((6123121759853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT233 (i+1))
      = (∑ i ∈ Finset.range 5, stT233 (i+1)) + stT233 6 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 5
    simpa using h
  have hprev := st233_p5
  have hstep := st233_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p7 : ((1419903608977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT233 (i+1))
      = (∑ i ∈ Finset.range 6, stT233 (i+1)) + stT233 7 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 6
    simpa using h
  have hprev := st233_p6
  have hstep := st233_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p8 : ((791461750037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT233 (i+1))
      = (∑ i ∈ Finset.range 7, stT233 (i+1)) + stT233 8 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 7
    simpa using h
  have hprev := st233_p7
  have hstep := st233_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p9 : ((1748695050051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT233 (i+1))
      = (∑ i ∈ Finset.range 8, stT233 (i+1)) + stT233 9 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 8
    simpa using h
  have hprev := st233_p8
  have hstep := st233_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p10 : ((168160045149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT233 (i+1))
      = (∑ i ∈ Finset.range 9, stT233 (i+1)) + stT233 10 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 9
    simpa using h
  have hprev := st233_p9
  have hstep := st233_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p11 : ((3298864595143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT233 (i+1))
      = (∑ i ∈ Finset.range 10, stT233 (i+1)) + stT233 11 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 10
    simpa using h
  have hprev := st233_p10
  have hstep := st233_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p12 : ((636633292347/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT233 (i+1))
      = (∑ i ∈ Finset.range 11, stT233 (i+1)) + stT233 12 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 11
    simpa using h
  have hprev := st233_p11
  have hstep := st233_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p13 : ((724742395047/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT233 (i+1))
      = (∑ i ∈ Finset.range 12, stT233 (i+1)) + stT233 13 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 12
    simpa using h
  have hprev := st233_p12
  have hstep := st233_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p14 : ((6257135465479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT233 (i+1))
      = (∑ i ∈ Finset.range 13, stT233 (i+1)) + stT233 14 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 13
    simpa using h
  have hprev := st233_p13
  have hstep := st233_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p15 : ((74491263059/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT233 (i+1))
      = (∑ i ∈ Finset.range 14, stT233 (i+1)) + stT233 15 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 14
    simpa using h
  have hprev := st233_p14
  have hstep := st233_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p16 : ((118970013059/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT233 (i+1))
      = (∑ i ∈ Finset.range 15, stT233 (i+1)) + stT233 16 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 15
    simpa using h
  have hprev := st233_p15
  have hstep := st233_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p17 : ((3540523658033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT233 (i+1))
      = (∑ i ∈ Finset.range 16, stT233 (i+1)) + stT233 17 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 16
    simpa using h
  have hprev := st233_p16
  have hstep := st233_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p18 : ((807771651881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT233 (i+1))
      = (∑ i ∈ Finset.range 17, stT233 (i+1)) + stT233 18 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 17
    simpa using h
  have hprev := st233_p17
  have hstep := st233_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p19 : ((1447713028193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT233 (i+1))
      = (∑ i ∈ Finset.range 18, stT233 (i+1)) + stT233 19 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 18
    simpa using h
  have hprev := st233_p18
  have hstep := st233_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p20 : ((1622533218387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT233 (i+1))
      = (∑ i ∈ Finset.range 19, stT233 (i+1)) + stT233 20 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 19
    simpa using h
  have hprev := st233_p19
  have hstep := st233_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p21 : ((866896995903/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT233 (i+1))
      = (∑ i ∈ Finset.range 20, stT233 (i+1)) + stT233 21 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 20
    simpa using h
  have hprev := st233_p20
  have hstep := st233_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p22 : ((4225900746071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT233 (i+1))
      = (∑ i ∈ Finset.range 21, stT233 (i+1)) + stT233 22 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 21
    simpa using h
  have hprev := st233_p21
  have hstep := st233_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p23 : ((6912295150597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT233 (i+1))
      = (∑ i ∈ Finset.range 22, stT233 (i+1)) + stT233 23 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 22
    simpa using h
  have hprev := st233_p22
  have hstep := st233_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p24 : ((555664961979/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT233 (i+1))
      = (∑ i ∈ Finset.range 23, stT233 (i+1)) + stT233 24 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 23
    simpa using h
  have hprev := st233_p23
  have hstep := st233_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p25 : ((6916704404697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT233 (i+1))
      = (∑ i ∈ Finset.range 24, stT233 (i+1)) + stT233 25 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 24
    simpa using h
  have hprev := st233_p24
  have hstep := st233_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p26 : ((2170995766769/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT233 (i+1))
      = (∑ i ∈ Finset.range 25, stT233 (i+1)) + stT233 26 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 25
    simpa using h
  have hprev := st233_p25
  have hstep := st233_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p27 : ((3888049860163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT233 (i+1))
      = (∑ i ∈ Finset.range 26, stT233 (i+1)) + stT233 27 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 26
    simpa using h
  have hprev := st233_p26
  have hstep := st233_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p28 : ((3468607424959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT233 (i+1))
      = (∑ i ∈ Finset.range 27, stT233 (i+1)) + stT233 28 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 27
    simpa using h
  have hprev := st233_p27
  have hstep := st233_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p29 : ((1755304987893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT233 (i+1))
      = (∑ i ∈ Finset.range 28, stT233 (i+1)) + stT233 29 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 28
    simpa using h
  have hprev := st233_p28
  have hstep := st233_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p30 : ((8945124817851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT233 (i+1))
      = (∑ i ∈ Finset.range 29, stT233 (i+1)) + stT233 30 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 29
    simpa using h
  have hprev := st233_p29
  have hstep := st233_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p31 : ((7232664559173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT233 (i+1))
      = (∑ i ∈ Finset.range 30, stT233 (i+1)) + stT233 31 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 30
    simpa using h
  have hprev := st233_p30
  have hstep := st233_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p32 : ((3005444153513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT233 (i+1))
      = (∑ i ∈ Finset.range 31, stT233 (i+1)) + stT233 32 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 31
    simpa using h
  have hprev := st233_p31
  have hstep := st233_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p33 : ((3112707289081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT233 (i+1))
      = (∑ i ∈ Finset.range 32, stT233 (i+1)) + stT233 33 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 32
    simpa using h
  have hprev := st233_p32
  have hstep := st233_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p34 : ((3725495439371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT233 (i+1))
      = (∑ i ∈ Finset.range 33, stT233 (i+1)) + stT233 34 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 33
    simpa using h
  have hprev := st233_p33
  have hstep := st233_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p35 : ((4531922792783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT233 (i+1))
      = (∑ i ∈ Finset.range 34, stT233 (i+1)) + stT233 35 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 34
    simpa using h
  have hprev := st233_p34
  have hstep := st233_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p36 : ((2682495813111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT233 (i+1))
      = (∑ i ∈ Finset.range 35, stT233 (i+1)) + stT233 36 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 35
    simpa using h
  have hprev := st233_p35
  have hstep := st233_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p37 : ((1236893178217/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT233 (i+1))
      = (∑ i ∈ Finset.range 36, stT233 (i+1)) + stT233 37 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 36
    simpa using h
  have hprev := st233_p36
  have hstep := st233_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p38 : ((6995504758097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT233 (i+1))
      = (∑ i ∈ Finset.range 37, stT233 (i+1)) + stT233 38 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 37
    simpa using h
  have hprev := st233_p37
  have hstep := st233_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p39 : ((1944083152071/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT233 (i+1))
      = (∑ i ∈ Finset.range 38, stT233 (i+1)) + stT233 39 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 38
    simpa using h
  have hprev := st233_p38
  have hstep := st233_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p40 : ((210642728679/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT233 (i+1))
      = (∑ i ∈ Finset.range 39, stT233 (i+1)) + stT233 40 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 39
    simpa using h
  have hprev := st233_p39
  have hstep := st233_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p41 : ((8754131506101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT233 (i+1))
      = (∑ i ∈ Finset.range 40, stT233 (i+1)) + stT233 41 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 40
    simpa using h
  have hprev := st233_p40
  have hstep := st233_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p42 : ((8574977543531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT233 (i+1))
      = (∑ i ∈ Finset.range 41, stT233 (i+1)) + stT233 42 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 41
    simpa using h
  have hprev := st233_p41
  have hstep := st233_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p43 : ((3959674349987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT233 (i+1))
      = (∑ i ∈ Finset.range 42, stT233 (i+1)) + stT233 43 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 42
    simpa using h
  have hprev := st233_p42
  have hstep := st233_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p44 : ((3611169383183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT233 (i+1))
      = (∑ i ∈ Finset.range 43, stT233 (i+1)) + stT233 44 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 43
    simpa using h
  have hprev := st233_p43
  have hstep := st233_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p45 : ((3561707931701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT233 (i+1))
      = (∑ i ∈ Finset.range 44, stT233 (i+1)) + stT233 45 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 44
    simpa using h
  have hprev := st233_p44
  have hstep := st233_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p46 : ((15510047577149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT233 (i+1))
      = (∑ i ∈ Finset.range 45, stT233 (i+1)) + stT233 46 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 45
    simpa using h
  have hprev := st233_p45
  have hstep := st233_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p47 : ((16596472690733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT233 (i+1))
      = (∑ i ∈ Finset.range 46, stT233 (i+1)) + stT233 47 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 46
    simpa using h
  have hprev := st233_p46
  have hstep := st233_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p48 : ((15857520470397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT233 (i+1))
      = (∑ i ∈ Finset.range 47, stT233 (i+1)) + stT233 48 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 47
    simpa using h
  have hprev := st233_p47
  have hstep := st233_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p49 : ((14568327097577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT233 (i+1))
      = (∑ i ∈ Finset.range 48, stT233 (i+1)) + stT233 49 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 48
    simpa using h
  have hprev := st233_p48
  have hstep := st233_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p50 : ((15184231001207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT233 (i+1))
      = (∑ i ∈ Finset.range 49, stT233 (i+1)) + stT233 50 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 49
    simpa using h
  have hprev := st233_p49
  have hstep := st233_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p51 : ((16378633433927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT233 (i+1))
      = (∑ i ∈ Finset.range 50, stT233 (i+1)) + stT233 51 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 50
    simpa using h
  have hprev := st233_p50
  have hstep := st233_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p52 : ((7723277548773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT233 (i+1))
      = (∑ i ∈ Finset.range 51, stT233 (i+1)) + stT233 52 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 51
    simpa using h
  have hprev := st233_p51
  have hstep := st233_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p53 : ((3679321080211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT233 (i+1))
      = (∑ i ∈ Finset.range 52, stT233 (i+1)) + stT233 53 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 52
    simpa using h
  have hprev := st233_p52
  have hstep := st233_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p54 : ((1605023886223/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT233 (i+1))
      = (∑ i ∈ Finset.range 53, stT233 (i+1)) + stT233 54 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 53
    simpa using h
  have hprev := st233_p53
  have hstep := st233_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p55 : ((1573678844983/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT233 (i+1))
      = (∑ i ∈ Finset.range 54, stT233 (i+1)) + stT233 55 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 54
    simpa using h
  have hprev := st233_p54
  have hstep := st233_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p56 : ((14757717736447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT233 (i+1))
      = (∑ i ∈ Finset.range 55, stT233 (i+1)) + stT233 56 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 55
    simpa using h
  have hprev := st233_p55
  have hstep := st233_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p57 : ((16046153590383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT233 (i+1))
      = (∑ i ∈ Finset.range 56, stT233 (i+1)) + stT233 57 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 56
    simpa using h
  have hprev := st233_p56
  have hstep := st233_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p58 : ((15503106672203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT233 (i+1))
      = (∑ i ∈ Finset.range 57, stT233 (i+1)) + stT233 58 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 57
    simpa using h
  have hprev := st233_p57
  have hstep := st233_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p59 : ((14978033604963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT233 (i+1))
      = (∑ i ∈ Finset.range 58, stT233 (i+1)) + stT233 59 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 58
    simpa using h
  have hprev := st233_p58
  have hstep := st233_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p60 : ((16176269686063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT233 (i+1))
      = (∑ i ∈ Finset.range 59, stT233 (i+1)) + stT233 60 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 59
    simpa using h
  have hprev := st233_p59
  have hstep := st233_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p61 : ((1870536769617/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT233 (i+1))
      = (∑ i ∈ Finset.range 60, stT233 (i+1)) + stT233 61 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 60
    simpa using h
  have hprev := st233_p60
  have hstep := st233_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p62 : ((15676298627569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT233 (i+1))
      = (∑ i ∈ Finset.range 61, stT233 (i+1)) + stT233 62 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 61
    simpa using h
  have hprev := st233_p61
  have hstep := st233_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p63 : ((15665263321131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT233 (i+1))
      = (∑ i ∈ Finset.range 62, stT233 (i+1)) + stT233 63 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 62
    simpa using h
  have hprev := st233_p62
  have hstep := st233_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p64 : ((940320567189/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT233 (i+1))
      = (∑ i ∈ Finset.range 63, stT233 (i+1)) + stT233 64 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 63
    simpa using h
  have hprev := st233_p63
  have hstep := st233_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p65 : ((8040993613449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT233 (i+1))
      = (∑ i ∈ Finset.range 64, stT233 (i+1)) + stT233 65 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 64
    simpa using h
  have hprev := st233_p64
  have hstep := st233_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p66 : ((7433876793489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT233 (i+1))
      = (∑ i ∈ Finset.range 65, stT233 (i+1)) + stT233 66 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 65
    simpa using h
  have hprev := st233_p65
  have hstep := st233_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p67 : ((8032864809831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT233 (i+1))
      = (∑ i ∈ Finset.range 66, stT233 (i+1)) + stT233 67 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 66
    simpa using h
  have hprev := st233_p66
  have hstep := st233_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p68 : ((15005798453823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT233 (i+1))
      = (∑ i ∈ Finset.range 67, stT233 (i+1)) + stT233 68 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 67
    simpa using h
  have hprev := st233_p67
  have hstep := st233_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p69 : ((15872203017843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT233 (i+1))
      = (∑ i ∈ Finset.range 68, stT233 (i+1)) + stT233 69 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 68
    simpa using h
  have hprev := st233_p68
  have hstep := st233_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p70 : ((7602364289011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT233 (i+1))
      = (∑ i ∈ Finset.range 69, stT233 (i+1)) + stT233 70 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 69
    simpa using h
  have hprev := st233_p69
  have hstep := st233_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p71 : ((3139672365501/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT233 (i+1))
      = (∑ i ∈ Finset.range 70, stT233 (i+1)) + stT233 71 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 70
    simpa using h
  have hprev := st233_p70
  have hstep := st233_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p72 : ((15336746026913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT233 (i+1))
      = (∑ i ∈ Finset.range 71, stT233 (i+1)) + stT233 72 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 71
    simpa using h
  have hprev := st233_p71
  have hstep := st233_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p73 : ((15614411991731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT233 (i+1))
      = (∑ i ∈ Finset.range 72, stT233 (i+1)) + stT233 73 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 72
    simpa using h
  have hprev := st233_p72
  have hstep := st233_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p74 : ((3074163452267/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT233 (i+1))
      = (∑ i ∈ Finset.range 73, stT233 (i+1)) + stT233 74 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 73
    simpa using h
  have hprev := st233_p73
  have hstep := st233_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p75 : ((3125692170707/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT233 (i+1))
      = (∑ i ∈ Finset.range 74, stT233 (i+1)) + stT233 75 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 74
    simpa using h
  have hprev := st233_p74
  have hstep := st233_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p76 : ((3827703794523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT233 (i+1))
      = (∑ i ∈ Finset.range 75, stT233 (i+1)) + stT233 76 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 75
    simpa using h
  have hprev := st233_p75
  have hstep := st233_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p77 : ((3932392468243/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT233 (i+1))
      = (∑ i ∈ Finset.range 76, stT233 (i+1)) + stT233 77 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 76
    simpa using h
  have hprev := st233_p76
  have hstep := st233_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p78 : ((3793837873939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT233 (i+1))
      = (∑ i ∈ Finset.range 77, stT233 (i+1)) + stT233 78 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 77
    simpa using h
  have hprev := st233_p77
  have hstep := st233_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p79 : ((15886961147647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT233 (i+1))
      = (∑ i ∈ Finset.range 78, stT233 (i+1)) + stT233 79 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 78
    simpa using h
  have hprev := st233_p78
  have hstep := st233_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p80 : ((15014210390839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT233 (i+1))
      = (∑ i ∈ Finset.range 79, stT233 (i+1)) + stT233 80 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 79
    simpa using h
  have hprev := st233_p79
  have hstep := st233_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p81 : ((16025003623093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT233 (i+1))
      = (∑ i ∈ Finset.range 80, stT233 (i+1)) + stT233 81 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 80
    simpa using h
  have hprev := st233_p80
  have hstep := st233_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p82 : ((14932288462673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT233 (i+1))
      = (∑ i ∈ Finset.range 81, stT233 (i+1)) + stT233 82 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 81
    simpa using h
  have hprev := st233_p81
  have hstep := st233_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p83 : ((16013700728061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT233 (i+1))
      = (∑ i ∈ Finset.range 82, stT233 (i+1)) + stT233 83 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 82
    simpa using h
  have hprev := st233_p82
  have hstep := st233_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p84 : ((15068426177841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT233 (i+1))
      = (∑ i ∈ Finset.range 83, stT233 (i+1)) + stT233 84 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 83
    simpa using h
  have hprev := st233_p83
  have hstep := st233_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p85 : ((15736467683249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT233 (i+1))
      = (∑ i ∈ Finset.range 84, stT233 (i+1)) + stT233 85 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 84
    simpa using h
  have hprev := st233_p84
  have hstep := st233_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p86 : ((3094517360677/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT233 (i+1))
      = (∑ i ∈ Finset.range 85, stT233 (i+1)) + stT233 86 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 85
    simpa using h
  have hprev := st233_p85
  have hstep := st233_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p87 : ((15258768875117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT233 (i+1))
      = (∑ i ∈ Finset.range 86, stT233 (i+1)) + stT233 87 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 86
    simpa using h
  have hprev := st233_p86
  have hstep := st233_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p88 : ((995533993127/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT233 (i+1))
      = (∑ i ∈ Finset.range 87, stT233 (i+1)) + stT233 88 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 87
    simpa using h
  have hprev := st233_p87
  have hstep := st233_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p89 : ((7472557422781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT233 (i+1))
      = (∑ i ∈ Finset.range 88, stT233 (i+1)) + stT233 89 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 88
    simpa using h
  have hprev := st233_p88
  have hstep := st233_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p90 : ((1598640911459/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT233 (i+1))
      = (∑ i ∈ Finset.range 89, stT233 (i+1)) + stT233 90 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 89
    simpa using h
  have hprev := st233_p89
  have hstep := st233_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p91 : ((1520007795667/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT233 (i+1))
      = (∑ i ∈ Finset.range 90, stT233 (i+1)) + stT233 91 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 90
    simpa using h
  have hprev := st233_p90
  have hstep := st233_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p92 : ((309220466051/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT233 (i+1))
      = (∑ i ∈ Finset.range 91, stT233 (i+1)) + stT233 92 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 91
    simpa using h
  have hprev := st233_p91
  have hstep := st233_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p93 : ((7917791223581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT233 (i+1))
      = (∑ i ∈ Finset.range 92, stT233 (i+1)) + stT233 93 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 92
    simpa using h
  have hprev := st233_p92
  have hstep := st233_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p94 : ((7478537473597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT233 (i+1))
      = (∑ i ∈ Finset.range 93, stT233 (i+1)) + stT233 94 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 93
    simpa using h
  have hprev := st233_p93
  have hstep := st233_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p95 : ((3993768992061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT233 (i+1))
      = (∑ i ∈ Finset.range 94, stT233 (i+1)) + stT233 95 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 94
    simpa using h
  have hprev := st233_p94
  have hstep := st233_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p96 : ((7641670960263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT233 (i+1))
      = (∑ i ∈ Finset.range 95, stT233 (i+1)) + stT233 96 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 95
    simpa using h
  have hprev := st233_p95
  have hstep := st233_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p97 : ((191264249007/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT233 (i+1))
      = (∑ i ∈ Finset.range 96, stT233 (i+1)) + stT233 97 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 96
    simpa using h
  have hprev := st233_p96
  have hstep := st233_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p98 : ((1997240068421/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT233 (i+1))
      = (∑ i ∈ Finset.range 97, stT233 (i+1)) + stT233 98 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 97
    simpa using h
  have hprev := st233_p97
  have hstep := st233_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p99 : ((7487334249947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT233 (i+1))
      = (∑ i ∈ Finset.range 98, stT233 (i+1)) + stT233 99 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 98
    simpa using h
  have hprev := st233_p98
  have hstep := st233_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p100 : ((3928371440269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT233 (i+1))
      = (∑ i ∈ Finset.range 99, stT233 (i+1)) + stT233 100 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 99
    simpa using h
  have hprev := st233_p99
  have hstep := st233_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p101 : ((7852618945547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT233 (i+1))
      = (∑ i ∈ Finset.range 100, stT233 (i+1)) + stT233 101 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 100
    simpa using h
  have hprev := st233_p100
  have hstep := st233_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p102 : ((7484679453673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT233 (i+1))
      = (∑ i ∈ Finset.range 101, stT233 (i+1)) + stT233 102 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 101
    simpa using h
  have hprev := st233_p101
  have hstep := st233_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p103 : ((249150326717/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT233 (i+1))
      = (∑ i ∈ Finset.range 102, stT233 (i+1)) + stT233 103 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 102
    simpa using h
  have hprev := st233_p102
  have hstep := st233_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p104 : ((15437192603131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT233 (i+1))
      = (∑ i ∈ Finset.range 103, stT233 (i+1)) + stT233 104 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 103
    simpa using h
  have hprev := st233_p103
  have hstep := st233_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p105 : ((1508709690249/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT233 (i+1))
      = (∑ i ∈ Finset.range 104, stT233 (i+1)) + stT233 105 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 104
    simpa using h
  have hprev := st233_p104
  have hstep := st233_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p106 : ((3204583474657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT233 (i+1))
      = (∑ i ∈ Finset.range 105, stT233 (i+1)) + stT233 106 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 105
    simpa using h
  have hprev := st233_p105
  have hstep := st233_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p107 : ((3054584561737/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT233 (i+1))
      = (∑ i ∈ Finset.range 106, stT233 (i+1)) + stT233 107 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 106
    simpa using h
  have hprev := st233_p106
  have hstep := st233_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p108 : ((15190001791011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT233 (i+1))
      = (∑ i ∈ Finset.range 107, stT233 (i+1)) + stT233 108 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 107
    simpa using h
  have hprev := st233_p107
  have hstep := st233_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p109 : ((16034876159961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT233 (i+1))
      = (∑ i ∈ Finset.range 108, stT233 (i+1)) + stT233 109 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 108
    simpa using h
  have hprev := st233_p108
  have hstep := st233_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p110 : ((3802238284539/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT233 (i+1))
      = (∑ i ∈ Finset.range 109, stT233 (i+1)) + stT233 110 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 109
    simpa using h
  have hprev := st233_p109
  have hstep := st233_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p111 : ((475709872333/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT233 (i+1))
      = (∑ i ∈ Finset.range 110, stT233 (i+1)) + stT233 111 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 110
    simpa using h
  have hprev := st233_p110
  have hstep := st233_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p112 : ((1603629751441/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT233 (i+1))
      = (∑ i ∈ Finset.range 111, stT233 (i+1)) + stT233 112 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 111
    simpa using h
  have hprev := st233_p111
  have hstep := st233_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p113 : ((7613973623881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT233 (i+1))
      = (∑ i ∈ Finset.range 112, stT233 (i+1)) + stT233 113 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 112
    simpa using h
  have hprev := st233_p112
  have hstep := st233_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p114 : ((7588233430843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT233 (i+1))
      = (∑ i ∈ Finset.range 113, stT233 (i+1)) + stT233 114 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 113
    simpa using h
  have hprev := st233_p113
  have hstep := st233_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p115 : ((8015966021863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT233 (i+1))
      = (∑ i ∈ Finset.range 114, stT233 (i+1)) + stT233 115 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 114
    simpa using h
  have hprev := st233_p114
  have hstep := st233_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p116 : ((7665419530513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT233 (i+1))
      = (∑ i ∈ Finset.range 115, stT233 (i+1)) + stT233 116 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 115
    simpa using h
  have hprev := st233_p115
  have hstep := st233_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p117 : ((3014023921903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT233 (i+1))
      = (∑ i ∈ Finset.range 116, stT233 (i+1)) + stT233 117 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 116
    simpa using h
  have hprev := st233_p116
  have hstep := st233_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p118 : ((15983307844313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT233 (i+1))
      = (∑ i ∈ Finset.range 117, stT233 (i+1)) + stT233 118 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 117
    simpa using h
  have hprev := st233_p117
  have hstep := st233_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p119 : ((15526338893007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT233 (i+1))
      = (∑ i ∈ Finset.range 118, stT233 (i+1)) + stT233 119 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 118
    simpa using h
  have hprev := st233_p118
  have hstep := st233_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p120 : ((2337411013/1562500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT233 (i+1))
      = (∑ i ∈ Finset.range 119, stT233 (i+1)) + stT233 120 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 119
    simpa using h
  have hprev := st233_p119
  have hstep := st233_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p121 : ((1582592870761/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT233 (i+1))
      = (∑ i ∈ Finset.range 120, stT233 (i+1)) + stT233 121 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 120
    simpa using h
  have hprev := st233_p120
  have hstep := st233_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p122 : ((7894948634963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT233 (i+1))
      = (∑ i ∈ Finset.range 121, stT233 (i+1)) + stT233 122 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 121
    simpa using h
  have hprev := st233_p121
  have hstep := st233_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p123 : ((3737382727889/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT233 (i+1))
      = (∑ i ∈ Finset.range 122, stT233 (i+1)) + stT233 123 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 122
    simpa using h
  have hprev := st233_p122
  have hstep := st233_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p124 : ((775946843461/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT233 (i+1))
      = (∑ i ∈ Finset.range 123, stT233 (i+1)) + stT233 124 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 123
    simpa using h
  have hprev := st233_p123
  have hstep := st233_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p125 : ((16011471879737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT233 (i+1))
      = (∑ i ∈ Finset.range 124, stT233 (i+1)) + stT233 125 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 124
    simpa using h
  have hprev := st233_p124
  have hstep := st233_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p126 : ((3031934540011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT233 (i+1))
      = (∑ i ∈ Finset.range 125, stT233 (i+1)) + stT233 126 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 125
    simpa using h
  have hprev := st233_p125
  have hstep := st233_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p127 : ((15136257123539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT233 (i+1))
      = (∑ i ∈ Finset.range 126, stT233 (i+1)) + stT233 127 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 126
    simpa using h
  have hprev := st233_p126
  have hstep := st233_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p128 : ((127974034777/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT233 (i+1))
      = (∑ i ∈ Finset.range 127, stT233 (i+1)) + stT233 128 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 127
    simpa using h
  have hprev := st233_p127
  have hstep := st233_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p129 : ((7797890997029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT233 (i+1))
      = (∑ i ∈ Finset.range 128, stT233 (i+1)) + stT233 129 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 128
    simpa using h
  have hprev := st233_p128
  have hstep := st233_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p130 : ((466425388799/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT233 (i+1))
      = (∑ i ∈ Finset.range 129, stT233 (i+1)) + stT233 130 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 129
    simpa using h
  have hprev := st233_p129
  have hstep := st233_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p131 : ((1952312378781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT233 (i+1))
      = (∑ i ∈ Finset.range 130, stT233 (i+1)) + stT233 131 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 130
    simpa using h
  have hprev := st233_p130
  have hstep := st233_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p132 : ((4000014277631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT233 (i+1))
      = (∑ i ∈ Finset.range 131, stT233 (i+1)) + stT233 132 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 131
    simpa using h
  have hprev := st233_p131
  have hstep := st233_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p133 : ((236928640061/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT233 (i+1))
      = (∑ i ∈ Finset.range 132, stT233 (i+1)) + stT233 133 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 132
    simpa using h
  have hprev := st233_p132
  have hstep := st233_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p134 : ((15084351804037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT233 (i+1))
      = (∑ i ∈ Finset.range 133, stT233 (i+1)) + stT233 134 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 133
    simpa using h
  have hprev := st233_p133
  have hstep := st233_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p135 : ((15942867313009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT233 (i+1))
      = (∑ i ∈ Finset.range 134, stT233 (i+1)) + stT233 135 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 134
    simpa using h
  have hprev := st233_p134
  have hstep := st233_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p136 : ((15756787902037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT233 (i+1))
      = (∑ i ∈ Finset.range 135, stT233 (i+1)) + stT233 136 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 135
    simpa using h
  have hprev := st233_p135
  have hstep := st233_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p137 : ((598224923419/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT233 (i+1))
      = (∑ i ∈ Finset.range 136, stT233 (i+1)) + stT233 137 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 136
    simpa using h
  have hprev := st233_p136
  have hstep := st233_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p138 : ((3069526145951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT233 (i+1))
      = (∑ i ∈ Finset.range 137, stT233 (i+1)) + stT233 138 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 137
    simpa using h
  have hprev := st233_p137
  have hstep := st233_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p139 : ((3210461912219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT233 (i+1))
      = (∑ i ∈ Finset.range 138, stT233 (i+1)) + stT233 139 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 138
    simpa using h
  have hprev := st233_p138
  have hstep := st233_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p140 : ((387863583767/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT233 (i+1))
      = (∑ i ∈ Finset.range 139, stT233 (i+1)) + stT233 140 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 139
    simpa using h
  have hprev := st233_p139
  have hstep := st233_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p141 : ((466066675273/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT233 (i+1))
      = (∑ i ∈ Finset.range 140, stT233 (i+1)) + stT233 141 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 140
    simpa using h
  have hprev := st233_p140
  have hstep := st233_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p142 : ((971639474483/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT233 (i+1))
      = (∑ i ∈ Finset.range 141, stT233 (i+1)) + stT233 142 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 141
    simpa using h
  have hprev := st233_p141
  have hstep := st233_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p143 : ((8027284443707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT233 (i+1))
      = (∑ i ∈ Finset.range 142, stT233 (i+1)) + stT233 143 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 142
    simpa using h
  have hprev := st233_p142
  have hstep := st233_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p144 : ((960438385669/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT233 (i+1))
      = (∑ i ∈ Finset.range 143, stT233 (i+1)) + stT233 144 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 143
    simpa using h
  have hprev := st233_p143
  have hstep := st233_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p145 : ((14926629697389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT233 (i+1))
      = (∑ i ∈ Finset.range 144, stT233 (i+1)) + stT233 145 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 144
    simpa using h
  have hprev := st233_p144
  have hstep := st233_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p146 : ((7820681722337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT233 (i+1))
      = (∑ i ∈ Finset.range 145, stT233 (i+1)) + stT233 146 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 145
    simpa using h
  have hprev := st233_p145
  have hstep := st233_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p147 : ((4010749690219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT233 (i+1))
      = (∑ i ∈ Finset.range 146, stT233 (i+1)) + stT233 147 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 146
    simpa using h
  have hprev := st233_p146
  have hstep := st233_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p148 : ((3830376039389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT233 (i+1))
      = (∑ i ∈ Finset.range 147, stT233 (i+1)) + stT233 148 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 147
    simpa using h
  have hprev := st233_p147
  have hstep := st233_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p149 : ((746379928481/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT233 (i+1))
      = (∑ i ∈ Finset.range 148, stT233 (i+1)) + stT233 149 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 148
    simpa using h
  have hprev := st233_p148
  have hstep := st233_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p150 : ((3909655720581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT233 (i+1))
      = (∑ i ∈ Finset.range 149, stT233 (i+1)) + stT233 150 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 149
    simpa using h
  have hprev := st233_p149
  have hstep := st233_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p151 : ((2006810094643/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT233 (i+1))
      = (∑ i ∈ Finset.range 150, stT233 (i+1)) + stT233 151 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 150
    simpa using h
  have hprev := st233_p150
  have hstep := st233_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p152 : ((1921405288891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT233 (i+1))
      = (∑ i ∈ Finset.range 151, stT233 (i+1)) + stT233 152 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 151
    simpa using h
  have hprev := st233_p151
  have hstep := st233_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p153 : ((7453311377561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT233 (i+1))
      = (∑ i ∈ Finset.range 152, stT233 (i+1)) + stT233 153 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 152
    simpa using h
  have hprev := st233_p152
  have hstep := st233_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p154 : ((7770336257157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT233 (i+1))
      = (∑ i ∈ Finset.range 153, stT233 (i+1)) + stT233 154 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 153
    simpa using h
  have hprev := st233_p153
  have hstep := st233_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p155 : ((321498576257/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT233 (i+1))
      = (∑ i ∈ Finset.range 154, stT233 (i+1)) + stT233 155 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 154
    simpa using h
  have hprev := st233_p154
  have hstep := st233_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p156 : ((15517163060841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT233 (i+1))
      = (∑ i ∈ Finset.range 155, stT233 (i+1)) + stT233 156 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 155
    simpa using h
  have hprev := st233_p155
  have hstep := st233_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p157 : ((14900928164661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT233 (i+1))
      = (∑ i ∈ Finset.range 156, stT233 (i+1)) + stT233 157 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 156
    simpa using h
  have hprev := st233_p156
  have hstep := st233_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p158 : ((7674140104001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT233 (i+1))
      = (∑ i ∈ Finset.range 157, stT233 (i+1)) + stT233 158 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 157
    simpa using h
  have hprev := st233_p157
  have hstep := st233_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p159 : ((16045539370763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT233 (i+1))
      = (∑ i ∈ Finset.range 158, stT233 (i+1)) + stT233 159 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 158
    simpa using h
  have hprev := st233_p158
  have hstep := st233_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p160 : ((15747489737343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT233 (i+1))
      = (∑ i ∈ Finset.range 159, stT233 (i+1)) + stT233 160 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 159
    simpa using h
  have hprev := st233_p159
  have hstep := st233_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p161 : ((14987351949177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT233 (i+1))
      = (∑ i ∈ Finset.range 160, stT233 (i+1)) + stT233 161 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 160
    simpa using h
  have hprev := st233_p160
  have hstep := st233_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p162 : ((3019289656759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT233 (i+1))
      = (∑ i ∈ Finset.range 161, stT233 (i+1)) + stT233 162 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 161
    simpa using h
  have hprev := st233_p161
  have hstep := st233_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p163 : ((3175933354203/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT233 (i+1))
      = (∑ i ∈ Finset.range 162, stT233 (i+1)) + stT233 163 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 162
    simpa using h
  have hprev := st233_p162
  have hstep := st233_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p164 : ((15991145048431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT233 (i+1))
      = (∑ i ∈ Finset.range 163, stT233 (i+1)) + stT233 164 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 163
    simpa using h
  have hprev := st233_p163
  have hstep := st233_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p165 : ((15246848623497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT233 (i+1))
      = (∑ i ∈ Finset.range 164, stT233 (i+1)) + stT233 165 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 164
    simpa using h
  have hprev := st233_p164
  have hstep := st233_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p166 : ((14901799830333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT233 (i+1))
      = (∑ i ∈ Finset.range 165, stT233 (i+1)) + stT233 166 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 165
    simpa using h
  have hprev := st233_p165
  have hstep := st233_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p167 : ((3105223116759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT233 (i+1))
      = (∑ i ∈ Finset.range 166, stT233 (i+1)) + stT233 167 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 166
    simpa using h
  have hprev := st233_p166
  have hstep := st233_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p168 : ((16085816495091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT233 (i+1))
      = (∑ i ∈ Finset.range 167, stT233 (i+1)) + stT233 168 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 167
    simpa using h
  have hprev := st233_p167
  have hstep := st233_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p169 : ((3134000812531/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT233 (i+1))
      = (∑ i ∈ Finset.range 168, stT233 (i+1)) + stT233 169 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 168
    simpa using h
  have hprev := st233_p168
  have hstep := st233_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p170 : ((2991252673159/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT233 (i+1))
      = (∑ i ∈ Finset.range 169, stT233 (i+1)) + stT233 170 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 169
    simpa using h
  have hprev := st233_p169
  have hstep := st233_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p171 : ((15086088180987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT233 (i+1))
      = (∑ i ∈ Finset.range 170, stT233 (i+1)) + stT233 171 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 170
    simpa using h
  have hprev := st233_p170
  have hstep := st233_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p172 : ((15847884025791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT233 (i+1))
      = (∑ i ∈ Finset.range 171, stT233 (i+1)) + stT233 172 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 171
    simpa using h
  have hprev := st233_p171
  have hstep := st233_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p173 : ((16044493726791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT233 (i+1))
      = (∑ i ∈ Finset.range 172, stT233 (i+1)) + stT233 173 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 172
    simpa using h
  have hprev := st233_p172
  have hstep := st233_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p174 : ((15375374322619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT233 (i+1))
      = (∑ i ∈ Finset.range 173, stT233 (i+1)) + stT233 174 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 173
    simpa using h
  have hprev := st233_p173
  have hstep := st233_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p175 : ((1487404145389/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT233 (i+1))
      = (∑ i ∈ Finset.range 174, stT233 (i+1)) + stT233 175 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 174
    simpa using h
  have hprev := st233_p174
  have hstep := st233_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p176 : ((1912655359257/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT233 (i+1))
      = (∑ i ∈ Finset.range 175, stT233 (i+1)) + stT233 176 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 175
    simpa using h
  have hprev := st233_p175
  have hstep := st233_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p177 : ((8003388823447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT233 (i+1))
      = (∑ i ∈ Finset.range 176, stT233 (i+1)) + stT233 177 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 176
    simpa using h
  have hprev := st233_p176
  have hstep := st233_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p178 : ((7968258633373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT233 (i+1))
      = (∑ i ∈ Finset.range 177, stT233 (i+1)) + stT233 178 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 177
    simpa using h
  have hprev := st233_p177
  have hstep := st233_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p179 : ((7600012986047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT233 (i+1))
      = (∑ i ∈ Finset.range 178, stT233 (i+1)) + stT233 179 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 178
    simpa using h
  have hprev := st233_p178
  have hstep := st233_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p180 : ((1487955717847/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT233 (i+1))
      = (∑ i ∈ Finset.range 179, stT233 (i+1)) + stT233 180 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 179
    simpa using h
  have hprev := st233_p179
  have hstep := st233_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p181 : ((7718105770829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT233 (i+1))
      = (∑ i ∈ Finset.range 180, stT233 (i+1)) + stT233 181 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 180
    simpa using h
  have hprev := st233_p180
  have hstep := st233_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p182 : ((3212885941079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT233 (i+1))
      = (∑ i ∈ Finset.range 181, stT233 (i+1)) + stT233 182 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 181
    simpa using h
  have hprev := st233_p181
  have hstep := st233_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p183 : ((15870536210127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT233 (i+1))
      = (∑ i ∈ Finset.range 182, stT233 (i+1)) + stT233 183 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 182
    simpa using h
  have hprev := st233_p182
  have hstep := st233_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p184 : ((15133758952397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT233 (i+1))
      = (∑ i ∈ Finset.range 183, stT233 (i+1)) + stT233 184 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 183
    simpa using h
  have hprev := st233_p183
  have hstep := st233_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p185 : ((14886040021587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT233 (i+1))
      = (∑ i ∈ Finset.range 184, stT233 (i+1)) + stT233 185 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 184
    simpa using h
  have hprev := st233_p184
  have hstep := st233_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p186 : ((15465996644247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT233 (i+1))
      = (∑ i ∈ Finset.range 185, stT233 (i+1)) + stT233 186 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 185
    simpa using h
  have hprev := st233_p185
  have hstep := st233_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p187 : ((16073195917823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT233 (i+1))
      = (∑ i ∈ Finset.range 186, stT233 (i+1)) + stT233 187 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 186
    simpa using h
  have hprev := st233_p186
  have hstep := st233_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p188 : ((7941823269149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT233 (i+1))
      = (∑ i ∈ Finset.range 187, stT233 (i+1)) + stT233 188 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 187
    simpa using h
  have hprev := st233_p187
  have hstep := st233_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p189 : ((3789523460647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT233 (i+1))
      = (∑ i ∈ Finset.range 188, stT233 (i+1)) + stT233 189 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 188
    simpa using h
  have hprev := st233_p188
  have hstep := st233_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p190 : ((14866814101611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT233 (i+1))
      = (∑ i ∈ Finset.range 189, stT233 (i+1)) + stT233 190 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 189
    simpa using h
  have hprev := st233_p189
  have hstep := st233_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p191 : ((15390858229667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT233 (i+1))
      = (∑ i ∈ Finset.range 190, stT233 (i+1)) + stT233 191 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 190
    simpa using h
  have hprev := st233_p190
  have hstep := st233_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p192 : ((16038794591763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT233 (i+1))
      = (∑ i ∈ Finset.range 191, stT233 (i+1)) + stT233 192 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 191
    simpa using h
  have hprev := st233_p191
  have hstep := st233_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p193 : ((15970114067939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT233 (i+1))
      = (∑ i ∈ Finset.range 192, stT233 (i+1)) + stT233 193 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 192
    simpa using h
  have hprev := st233_p192
  have hstep := st233_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p194 : ((7639174901027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT233 (i+1))
      = (∑ i ∈ Finset.range 193, stT233 (i+1)) + stT233 194 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 193
    simpa using h
  have hprev := st233_p193
  have hstep := st233_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p195 : ((7424181423497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT233 (i+1))
      = (∑ i ∈ Finset.range 194, stT233 (i+1)) + stT233 195 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 194
    simpa using h
  have hprev := st233_p194
  have hstep := st233_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p196 : ((1902543702233/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT233 (i+1))
      = (∑ i ∈ Finset.range 195, stT233 (i+1)) + stT233 196 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 195
    simpa using h
  have hprev := st233_p195
  have hstep := st233_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p197 : ((7961682214247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT233 (i+1))
      = (∑ i ∈ Finset.range 196, stT233 (i+1)) + stT233 197 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 196
    simpa using h
  have hprev := st233_p196
  have hstep := st233_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p198 : ((8042070248851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT233 (i+1))
      = (∑ i ∈ Finset.range 197, stT233 (i+1)) + stT233 198 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 197
    simpa using h
  have hprev := st233_p197
  have hstep := st233_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p199 : ((7754665384063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT233 (i+1))
      = (∑ i ∈ Finset.range 198, stT233 (i+1)) + stT233 199 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 198
    simpa using h
  have hprev := st233_p198
  have hstep := st233_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p200 : ((1862971779103/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT233 (i+1))
      = (∑ i ∈ Finset.range 199, stT233 (i+1)) + stT233 200 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 199
    simpa using h
  have hprev := st233_p199
  have hstep := st233_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p201 : ((14997958245329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT233 (i+1))
      = (∑ i ∈ Finset.range 200, stT233 (i+1)) + stT233 201 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 200
    simpa using h
  have hprev := st233_p200
  have hstep := st233_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p202 : ((7837009988367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT233 (i+1))
      = (∑ i ∈ Finset.range 201, stT233 (i+1)) + stT233 202 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 201
    simpa using h
  have hprev := st233_p201
  have hstep := st233_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p203 : ((1612650198579/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT233 (i+1))
      = (∑ i ∈ Finset.range 202, stT233 (i+1)) + stT233 203 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 202
    simpa using h
  have hprev := st233_p202
  have hstep := st233_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p204 : ((15825540075671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT233 (i+1))
      = (∑ i ∈ Finset.range 203, stT233 (i+1)) + stT233 204 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 203
    simpa using h
  have hprev := st233_p203
  have hstep := st233_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p205 : ((7563566061947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT233 (i+1))
      = (∑ i ∈ Finset.range 204, stT233 (i+1)) + stT233 205 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 204
    simpa using h
  have hprev := st233_p204
  have hstep := st233_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p206 : ((296807601969/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT233 (i+1))
      = (∑ i ∈ Finset.range 205, stT233 (i+1)) + stT233 206 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 205
    simpa using h
  have hprev := st233_p205
  have hstep := st233_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p207 : ((7645170483869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT233 (i+1))
      = (∑ i ∈ Finset.range 206, stT233 (i+1)) + stT233 207 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 206
    simpa using h
  have hprev := st233_p206
  have hstep := st233_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p208 : ((1995128765561/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT233 (i+1))
      = (∑ i ∈ Finset.range 207, stT233 (i+1)) + stT233 208 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 207
    simpa using h
  have hprev := st233_p207
  have hstep := st233_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p209 : ((8048182330151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT233 (i+1))
      = (∑ i ∈ Finset.range 208, stT233 (i+1)) + stT233 209 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 208
    simpa using h
  have hprev := st233_p208
  have hstep := st233_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p210 : ((1943665303691/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT233 (i+1))
      = (∑ i ∈ Finset.range 209, stT233 (i+1)) + stT233 210 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 209
    simpa using h
  have hprev := st233_p209
  have hstep := st233_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p211 : ((14929783831129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT233 (i+1))
      = (∑ i ∈ Finset.range 210, stT233 (i+1)) + stT233 211 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 210
    simpa using h
  have hprev := st233_p210
  have hstep := st233_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p212 : ((2983498286207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT233 (i+1))
      = (∑ i ∈ Finset.range 211, stT233 (i+1)) + stT233 212 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 211
    simpa using h
  have hprev := st233_p211
  have hstep := st233_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p213 : ((3104264041583/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT233 (i+1))
      = (∑ i ∈ Finset.range 212, stT233 (i+1)) + stT233 213 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 212
    simpa using h
  have hprev := st233_p212
  have hstep := st233_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p214 : ((12567023311/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT233 (i+1))
      = (∑ i ∈ Finset.range 213, stT233 (i+1)) + stT233 214 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 213
    simpa using h
  have hprev := st233_p213
  have hstep := st233_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p215 : ((3201550239243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT233 (i+1))
      = (∑ i ∈ Finset.range 214, stT233 (i+1)) + stT233 215 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 214
    simpa using h
  have hprev := st233_p214
  have hstep := st233_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p216 : ((15374575618579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT233 (i+1))
      = (∑ i ∈ Finset.range 215, stT233 (i+1)) + stT233 216 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 215
    simpa using h
  have hprev := st233_p215
  have hstep := st233_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p217 : ((1856984872383/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT233 (i+1))
      = (∑ i ∈ Finset.range 216, stT233 (i+1)) + stT233 217 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 216
    simpa using h
  have hprev := st233_p216
  have hstep := st233_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p218 : ((7495770259567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT233 (i+1))
      = (∑ i ∈ Finset.range 217, stT233 (i+1)) + stT233 218 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 217
    simpa using h
  have hprev := st233_p217
  have hstep := st233_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p219 : ((61080153603/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT233 (i+1))
      = (∑ i ∈ Finset.range 218, stT233 (i+1)) + stT233 219 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 218
    simpa using h
  have hprev := st233_p218
  have hstep := st233_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p220 : ((16125729578151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT233 (i+1))
      = (∑ i ∈ Finset.range 219, stT233 (i+1)) + stT233 220 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 219
    simpa using h
  have hprev := st233_p219
  have hstep := st233_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p221 : ((7981366082751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT233 (i+1))
      = (∑ i ∈ Finset.range 220, stT233 (i+1)) + stT233 221 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 220
    simpa using h
  have hprev := st233_p220
  have hstep := st233_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p222 : ((15316614019701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT233 (i+1))
      = (∑ i ∈ Finset.range 221, stT233 (i+1)) + stT233 222 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 221
    simpa using h
  have hprev := st233_p221
  have hstep := st233_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p223 : ((14837231674201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT233 (i+1))
      = (∑ i ∈ Finset.range 222, stT233 (i+1)) + stT233 223 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 222
    simpa using h
  have hprev := st233_p222
  have hstep := st233_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p224 : ((7499538853619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT233 (i+1))
      = (∑ i ∈ Finset.range 223, stT233 (i+1)) + stT233 224 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 223
    simpa using h
  have hprev := st233_p223
  have hstep := st233_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p225 : ((977388358423/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT233 (i+1))
      = (∑ i ∈ Finset.range 224, stT233 (i+1)) + stT233 225 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 224
    simpa using h
  have hprev := st233_p224
  have hstep := st233_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p226 : ((8063567185739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT233 (i+1))
      = (∑ i ∈ Finset.range 225, stT233 (i+1)) + stT233 226 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 225
    simpa using h
  have hprev := st233_p225
  have hstep := st233_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p227 : ((7996659492333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT233 (i+1))
      = (∑ i ∈ Finset.range 226, stT233 (i+1)) + stT233 227 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 226
    simpa using h
  have hprev := st233_p226
  have hstep := st233_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p228 : ((15369744934141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT233 (i+1))
      = (∑ i ∈ Finset.range 227, stT233 (i+1)) + stT233 228 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 227
    simpa using h
  have hprev := st233_p227
  have hstep := st233_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p229 : ((464194773851/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT233 (i+1))
      = (∑ i ∈ Finset.range 228, stT233 (i+1)) + stT233 229 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 228
    simpa using h
  have hprev := st233_p228
  have hstep := st233_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p230 : ((3733363823023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT233 (i+1))
      = (∑ i ∈ Finset.range 229, stT233 (i+1)) + stT233 230 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 229
    simpa using h
  have hprev := st233_p229
  have hstep := st233_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p231 : ((15528855548473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT233 (i+1))
      = (∑ i ∈ Finset.range 230, stT233 (i+1)) + stT233 231 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 230
    simpa using h
  have hprev := st233_p230
  have hstep := st233_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p232 : ((16082615998789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT233 (i+1))
      = (∑ i ∈ Finset.range 231, stT233 (i+1)) + stT233 232 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 231
    simpa using h
  have hprev := st233_p231
  have hstep := st233_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p233 : ((8041827182787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT233 (i+1))
      = (∑ i ∈ Finset.range 232, stT233 (i+1)) + stT233 233 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 232
    simpa using h
  have hprev := st233_p232
  have hstep := st233_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p234 : ((15534868006773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT233 (i+1))
      = (∑ i ∈ Finset.range 233, stT233 (i+1)) + stT233 234 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 233
    simpa using h
  have hprev := st233_p233
  have hstep := st233_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p235 : ((3734736636933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT233 (i+1))
      = (∑ i ∈ Finset.range 234, stT233 (i+1)) + stT233 235 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 234
    simpa using h
  have hprev := st233_p234
  have hstep := st233_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p236 : ((7416843719671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT233 (i+1))
      = (∑ i ∈ Finset.range 235, stT233 (i+1)) + stT233 236 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 235
    simpa using h
  have hprev := st233_p235
  have hstep := st233_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p237 : ((15309836456429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT233 (i+1))
      = (∑ i ∈ Finset.range 236, stT233 (i+1)) + stT233 237 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 236
    simpa using h
  have hprev := st233_p236
  have hstep := st233_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p238 : ((15940479637159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT233 (i+1))
      = (∑ i ∈ Finset.range 237, stT233 (i+1)) + stT233 238 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 237
    simpa using h
  have hprev := st233_p237
  have hstep := st233_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p239 : ((646751253819/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT233 (i+1))
      = (∑ i ∈ Finset.range 238, stT233 (i+1)) + stT233 239 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 238
    simpa using h
  have hprev := st233_p238
  have hstep := st233_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p240 : ((3159571120449/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT233 (i+1))
      = (∑ i ∈ Finset.range 239, stT233 (i+1)) + stT233 240 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 239
    simpa using h
  have hprev := st233_p239
  have hstep := st233_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p241 : ((7576849623201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT233 (i+1))
      = (∑ i ∈ Finset.range 240, stT233 (i+1)) + stT233 241 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 240
    simpa using h
  have hprev := st233_p240
  have hstep := st233_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p242 : ((7396445929551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT233 (i+1))
      = (∑ i ∈ Finset.range 241, stT233 (i+1)) + stT233 242 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 241
    simpa using h
  have hprev := st233_p241
  have hstep := st233_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p243 : ((7510905246301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT233 (i+1))
      = (∑ i ∈ Finset.range 242, stT233 (i+1)) + stT233 243 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 242
    simpa using h
  have hprev := st233_p242
  have hstep := st233_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p244 : ((7821112165157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT233 (i+1))
      = (∑ i ∈ Finset.range 243, stT233 (i+1)) + stT233 244 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 243
    simpa using h
  have hprev := st233_p243
  have hstep := st233_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p245 : ((8064592280889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT233 (i+1))
      = (∑ i ∈ Finset.range 244, stT233 (i+1)) + stT233 245 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 244
    simpa using h
  have hprev := st233_p244
  have hstep := st233_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p246 : ((1607674767899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT233 (i+1))
      = (∑ i ∈ Finset.range 245, stT233 (i+1)) + stT233 246 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 245
    simpa using h
  have hprev := st233_p245
  have hstep := st233_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p247 : ((97075269869/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT233 (i+1))
      = (∑ i ∈ Finset.range 246, stT233 (i+1)) + stT233 247 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 246
    simpa using h
  have hprev := st233_p246
  have hstep := st233_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p248 : ((7473338833603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT233 (i+1))
      = (∑ i ∈ Finset.range 247, stT233 (i+1)) + stT233 248 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 247
    simpa using h
  have hprev := st233_p247
  have hstep := st233_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p249 : ((1849882696007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT233 (i+1))
      = (∑ i ∈ Finset.range 248, stT233 (i+1)) + stT233 249 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 248
    simpa using h
  have hprev := st233_p248
  have hstep := st233_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_p250 : ((3801477437569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT233 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT233 (i+1))
      = (∑ i ∈ Finset.range 249, stT233 (i+1)) + stT233 250 := by
    have h := Finset.sum_range_succ (fun i => stT233 (i+1)) 249
    simpa using h
  have hprev := st233_p249
  have hstep := st233_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st233_s250 :
    |Real.sin (((233 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))
      - ((-382793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -2179879/10000000) (δ := 11673/1000000000) (ψ := -136127/200000) 233 205
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 233`** (evaluated boundary). -/
theorem station_233_sign : hardyG ((((233:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 233 250 (by norm_num) (by norm_num)
    ((-136127/200000 : ℚ) : ℝ)
  have hchain := st233_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT233 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((233 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-136127/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st233_c250
  have hsinb := abs_le.mp st233_s250
  have hbdy_lo : ((5630373590059/108578500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((233 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-136127/200000 : ℚ) : ℝ))) / 2
          - ((((233:ℕ)):ℝ))
            * Real.sin (((233 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-136127/200000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((233:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((233:ℝ) * Real.log (250:ℝ) - ((-136127/200000 : ℚ) : ℝ))) / 2
        - ((233:ℝ)) * Real.sin ((233:ℝ) * Real.log (250:ℝ) - ((-136127/200000 : ℚ) : ℝ))
        ≥ ((44512049/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((233:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((44512049/250000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((44512049/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((44512049/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((233:ℕ)):ℝ))+1) * (((((233:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((74866899943/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((3801477437569/2500000000000 : ℚ) : ℝ) + ((5630373590059/108578500000000 : ℚ) : ℝ)
      - ((74866899943/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-136127/200000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((233:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-136127/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((233:ℕ)):ℝ)))).re
      - Real.sin ((-136127/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((233:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((233:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((233:ℕ)):ℝ))
      = (((((233:ℕ)):ℝ)) * (Real.log ((((233:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((233:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_233
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
  have hθwin : |(((-136127/200000 : ℚ) : ℝ) + ((49:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((233:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((233:ℕ)):ℝ)))
    (φ := ((-136127/200000 : ℚ) : ℝ) + ((49:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-136127/200000 : ℚ) : ℝ) + ((49:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-136127/200000 : ℚ)) : ℝ) - Real.pi) + ((49:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-136127/200000 : ℚ)) : ℝ) - Real.pi) 49).1,
    (cos_sin_shift ((((-136127/200000 : ℚ)) : ℝ) - Real.pi) 49).2]
  exact cos_sin_flip ((-136127/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_233_sign
end AxiomAudit
