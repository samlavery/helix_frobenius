import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 335` (rung-335.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT335 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((335 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-685113/500000 : ℚ) : ℝ))

theorem st335_c1 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((49807/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 685113/2000000) (δ := 1/1000000000) (ψ := -685113/500000) 335 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t1 : ((24891/125000 : ℚ) : ℝ) ≤ stT335 1 := by
  have hc : ((24891/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24891/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((24891/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c2 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((228283/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1370831/5000000) (δ := 4209/250000000) (ψ := -685113/500000) 335 37
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t2 : ((1613850834611/5000000000000 : ℚ) : ℝ) ≤ stT335 2 := by
  have hc : ((228233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1613850834611/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((228233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c3 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((26499/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -814127/2500000) (δ := 677/40000000) (ψ := -685113/500000) 335 59
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t3 : ((76467147239/500000000000 : ℚ) : ℝ) ≤ stT335 3 := by
  have hc : ((26489/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76467147239/500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((26489/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c4 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((10624/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2057801/10000000) (δ := 1687/100000000) (ψ := -685113/500000) 335 74
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t4 : ((169959/500000 : ℚ) : ℝ) ≤ stT335 4 := by
  have hc : ((169959/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169959/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((169959/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c5 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((984199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445007/10000000) (δ := 1049/62500000) (ψ := -685113/500000) 335 86
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t5 : ((880204716273/2000000000000 : ℚ) : ℝ) ≤ stT335 5 := by
  have hc : ((984099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((880204716273/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((984099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c6 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-5351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3940369/10000000) (δ := 16891/1000000000) (ψ := -685113/500000) 335 96
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t6 : ((-22253614833/10000000000000 : ℚ) : ℝ) ≤ stT335 6 := by
  have hc : ((-5451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22253614833/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-5451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c7 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((489919/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31429/625000) (δ := 1053/62500000) (ψ := -685113/500000) 335 104
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t7 : ((462882606659/1250000000000 : ℚ) : ℝ) ≤ stT335 7 := by
  have hc : ((489869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462882606659/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((489869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c8 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((426373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68697/500000) (δ := 3381/200000000) (ψ := -685113/500000) 335 111
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t8 : ((1507279035159/5000000000000 : ℚ) : ℝ) ≤ stT335 8 := by
  have hc : ((426323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1507279035159/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((426323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c9 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-672049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5769423/10000000) (δ := 16861/1000000000) (ψ := -685113/500000) 335 117
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t9 : ((-1120248557383/5000000000000 : ℚ) : ℝ) ≤ stT335 9 := by
  have hc : ((-672149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1120248557383/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-672149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c10 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((248859/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119469/5000000) (δ := 8459/500000000) (ψ := -685113/500000) 335 123
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t10 : ((393441017509/1250000000000 : ℚ) : ℝ) ≤ stT335 10 := by
  have hc : ((124417/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((393441017509/1250000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((124417/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c11 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((45707/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1043539/10000000) (δ := 423/25000000) (ψ := -685113/500000) 335 128
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t11 : ((68898347163/250000000000 : ℚ) : ℝ) ≤ stT335 11 := by
  have hc : ((22851/25000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68898347163/250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((22851/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c12 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-137647/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462423/1000000) (δ := 2107/125000000) (ψ := -685113/500000) 335 133
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t12 : ((-12421784067/156250000000 : ℚ) : ℝ) ≤ stT335 12 := by
  have hc : ((-137697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12421784067/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-137697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c13 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((9859/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -210161/5000000) (δ := 3357/200000000) (ψ := -685113/500000) 335 137
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t13 : ((27341163/100000000 : ℚ) : ℝ) ≤ stT335 13 := by
  have hc : ((4929/5000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27341163/100000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((4929/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c14 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((444717/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47469/400000) (δ := 8407/500000000) (ψ := -685113/500000) 335 141
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t14 : ((297105590051/1250000000000 : ℚ) : ℝ) ≤ stT335 14 := by
  have hc : ((444667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297105590051/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((444667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c15 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-798027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194907/312500) (δ := 16943/1000000000) (ψ := -685113/500000) 335 145
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t15 : ((-2060755134603/10000000000000 : ℚ) : ℝ) ≤ stT335 15 := by
  have hc : ((-798127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2060755134603/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-798127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c16 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((192429/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 690079/10000000) (δ := 16939/1000000000) (ψ := -685113/500000) 335 148
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t16 : ((192409/800000 : ℚ) : ℝ) ≤ stT335 16 := by
  have hc : ((192409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192409/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((192409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c17 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-82087/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1084823/2500000) (δ := 16817/1000000000) (ψ := -685113/500000) 335 151
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t17 : ((-199211547909/5000000000000 : ℚ) : ℝ) ≤ stT335 17 := by
  have hc : ((-82137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199211547909/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-82137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c18 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-223509/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2542781/5000000) (δ := 33/1953125) (ψ := -685113/500000) 335 154
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t18 : ((-526933704857/5000000000000 : ℚ) : ℝ) ≤ stT335 18 := by
  have hc : ((-223559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-526933704857/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-223559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c19 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((135107/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3242953/10000000) (δ := 16929/1000000000) (ψ := -685113/500000) 335 157
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t19 : ((309841961949/5000000000000 : ℚ) : ℝ) ≤ stT335 19 := by
  have hc : ((135057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309841961949/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((135057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c20 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((186529/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461399/5000000) (δ := 339/20000000) (ψ := -685113/500000) 335 160
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t20 : ((417046620103/2000000000000 : ℚ) : ℝ) ≤ stT335 20 := by
  have hc : ((186509/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417046620103/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((186509/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c21 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-964399/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56132/78125) (δ := 16831/1000000000) (ψ := -685113/500000) 335 163
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t21 : ((-2104709463321/10000000000000 : ℚ) : ℝ) ≤ stT335 21 := by
  have hc : ((-964499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2104709463321/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-964499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c22 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((247417/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179839/5000000) (δ := 8443/500000000) (ψ := -685113/500000) 335 165
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t22 : ((16482546117/78125000000 : ℚ) : ℝ) ≤ stT335 22 := by
  have hc : ((15462/15625 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16482546117/78125000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((15462/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c23 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-391059/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3086067/5000000) (δ := 169/10000000) (ψ := -685113/500000) 335 167
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t23 : ((-163103795161/1000000000000 : ℚ) : ℝ) ≤ stT335 23 := by
  have hc : ((-391109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163103795161/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-391109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c24 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-262383/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5308091/10000000) (δ := 8411/500000000) (ψ := -685113/500000) 335 170
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t24 : ((-267844630893/2500000000000 : ℚ) : ℝ) ≤ stT335 24 := by
  have hc : ((-262433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267844630893/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-262433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c25 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((132067/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2535593/10000000) (δ := 16867/1000000000) (ψ := -685113/500000) 335 172
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t25 : ((66021/625000 : ℚ) : ℝ) ≤ stT335 25 := by
  have hc : ((66021/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66021/625000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((66021/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c26 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((452019/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1104183/10000000) (δ := 1047/62500000) (ψ := -685113/500000) 335 174
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t26 : ((886383976009/5000000000000 : ℚ) : ℝ) ≤ stT335 26 := by
  have hc : ((451969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((886383976009/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((451969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c27 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((233527/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28519/312500) (δ := 3373/200000000) (ψ := -685113/500000) 335 176
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t27 : ((449374599/2500000000 : ℚ) : ℝ) ≤ stT335 27 := by
  have hc : ((116751/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449374599/2500000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((116751/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c28 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((732891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -935293/5000000) (δ := 16779/1000000000) (ψ := -685113/500000) 335 178
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t28 : ((692422276601/5000000000000 : ℚ) : ℝ) ≤ stT335 28 := by
  have hc : ((732791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((692422276601/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((732791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c29 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((184/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3897549/10000000) (δ := 16809/1000000000) (ψ := -685113/500000) 335 180
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t29 : ((5420445807/2500000000000 : ℚ) : ℝ) ≤ stT335 29 := by
  have hc : ((2919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5420445807/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((2919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c30 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-232791/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6920969/10000000) (δ := 2101/125000000) (ψ := -685113/500000) 335 182
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t30 : ((-13283185921/78125000000 : ℚ) : ℝ) ≤ stT335 30 := by
  have hc : ((-14551/15625 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13283185921/78125000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-14551/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c31 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-354377/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4832609/10000000) (δ := 3363/200000000) (ψ := -685113/500000) 335 183
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t31 : ((-318329916879/5000000000000 : ℚ) : ℝ) ≤ stT335 31 := by
  have hc : ((-354477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318329916879/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-354477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c32 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((999997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6219/10000000) (δ := 1693/100000000) (ψ := -685113/500000) 335 185
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t32 : ((883791960051/5000000000000 : ℚ) : ℝ) ≤ stT335 32 := by
  have hc : ((999897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((883791960051/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((999897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c33 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-158091/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5638493/10000000) (δ := 16759/1000000000) (ψ := -685113/500000) 335 187
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t33 : ((-68811174033/625000000000 : ℚ) : ℝ) ≤ stT335 33 := by
  have hc : ((-39529/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68811174033/625000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-39529/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c34 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((10841/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3655431/10000000) (δ := 4213/250000000) (ψ := -685113/500000) 335 188
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t34 : ((3715000507/200000000000 : ℚ) : ℝ) ≤ stT335 34 := by
  have hc : ((10831/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3715000507/200000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((10831/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c35 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((88241/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -435433/1250000) (δ := 8383/500000000) (ψ := -685113/500000) 335 190
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t35 : ((37267488207/1250000000000 : ℚ) : ℝ) ≤ stT335 35 := by
  have hc : ((88191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37267488207/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((88191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c36 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-37749/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4401701/10000000) (δ := 1693/100000000) (ψ := -685113/500000) 335 191
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t36 : ((-62948345923/2000000000000 : ℚ) : ℝ) ≤ stT335 36 := by
  have hc : ((-37769/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62948345923/2000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-37769/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c37 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-56199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4067563/10000000) (δ := 4229/250000000) (ψ := -685113/500000) 335 193
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t37 : ((-9255499301/1000000000000 : ℚ) : ℝ) ≤ stT335 37 := by
  have hc : ((-56299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9255499301/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-56299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c38 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((65033/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 639773/2500000) (δ := 8447/500000000) (ψ := -685113/500000) 335 194
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t38 : ((105477165387/1250000000000 : ℚ) : ℝ) ≤ stT335 38 := by
  have hc : ((130041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105477165387/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((130041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c39 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-119393/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3551177/5000000) (δ := 8447/500000000) (ψ := -685113/500000) 335 196
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t39 : ((-191201877851/1250000000000 : ℚ) : ℝ) ≤ stT335 39 := by
  have hc : ((-238811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191201877851/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-238811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c40 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((400251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1606659/10000000) (δ := 4229/250000000) (ψ := -685113/500000) 335 197
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t40 : ((316386504369/2500000000000 : ℚ) : ℝ) ≤ stT335 40 := by
  have hc : ((400201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316386504369/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((400201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c41 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((11137/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 336543/1000000) (δ := 16823/1000000000) (ψ := -685113/500000) 335 198
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t41 : ((4346314071/125000000000 : ℚ) : ℝ) ≤ stT335 41 := by
  have hc : ((2783/12500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4346314071/125000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((2783/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c42 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-999983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7839207/10000000) (δ := 1693/100000000) (ψ := -685113/500000) 335 199
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t42 : ((-771581035911/5000000000000 : ℚ) : ℝ) ≤ stT335 42 := by
  have hc : ((-1000083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-771581035911/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-1000083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c43 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((2853/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1934963/5000000) (δ := 3369/200000000) (ψ := -685113/500000) 335 201
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t43 : ((1732687957/500000000000 : ℚ) : ℝ) ≤ stT335 43 := by
  have hc : ((5681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1732687957/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((5681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c44 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((247901/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -324183/10000000) (δ := 4213/250000000) (ψ := -685113/500000) 335 202
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t44 : ((23355434441/156250000000 : ℚ) : ℝ) ≤ stT335 44 := by
  have hc : ((61969/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23355434441/156250000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((61969/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c45 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((219851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2788823/10000000) (δ := 1059/62500000) (ψ := -685113/500000) 335 203
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t45 : ((327659768511/5000000000000 : ℚ) : ℝ) ≤ stT335 45 := by
  have hc : ((219801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327659768511/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((219801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c46 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-23387/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5488189/10000000) (δ := 8383/500000000) (ψ := -685113/500000) 335 204
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t46 : ((-1724407911/20000000000 : ℚ) : ℝ) ≤ stT335 46 := by
  have hc : ((-23391/40000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1724407911/20000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-23391/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c47 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-99969/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 973969/1250000) (δ := 16773/1000000000) (ψ := -685113/500000) 335 205
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t47 : ((-2916687367/20000000000 : ℚ) : ℝ) ≤ stT335 47 := by
  have hc : ((-99979/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2916687367/20000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-99979/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c48 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-147043/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374497/625000) (δ := 4197/250000000) (ψ := -685113/500000) 335 207
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t48 : ((-13266700293/125000000000 : ℚ) : ℝ) ≤ stT335 48 := by
  have hc : ((-147063/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13266700293/125000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-147063/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c49 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-50093/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -886267/2000000) (δ := 3379/200000000) (ψ := -685113/500000) 335 208
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t49 : ((-8949646437/312500000000 : ℚ) : ℝ) ≤ stT335 49 := by
  have hc : ((-25059/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8949646437/312500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-25059/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c50 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((69813/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1609727/5000000) (δ := 16901/1000000000) (ψ := -685113/500000) 335 209
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t50 : ((24673774211/625000000000 : ℚ) : ℝ) ≤ stT335 50 := by
  have hc : ((17447/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24673774211/625000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((17447/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c51 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((592131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2342739/10000000) (δ := 16909/1000000000) (ψ := -685113/500000) 335 210
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t51 : ((20725229217/250000000000 : ℚ) : ℝ) ≤ stT335 51 := by
  have hc : ((592031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20725229217/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((592031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c52 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((754951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -447011/2500000) (δ := 16787/1000000000) (ψ := -685113/500000) 335 211
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t52 : ((4187158497/40000000000 : ℚ) : ℝ) ≤ stT335 52 := by
  have hc : ((754851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4187158497/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((754851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c53 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((81547/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77157/500000) (δ := 16879/1000000000) (ψ := -685113/500000) 335 212
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t53 : ((22399926177/200000000000 : ℚ) : ℝ) ≤ stT335 53 := by
  have hc : ((81537/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22399926177/200000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((81537/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c54 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((401469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1596469/10000000) (δ := 16831/1000000000) (ψ := -685113/500000) 335 213
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t54 : ((546261813513/5000000000000 : ℚ) : ℝ) ≤ stT335 54 := by
  have hc : ((401419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546261813513/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((401419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c55 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((44659/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1937061/10000000) (δ := 8419/500000000) (ψ := -685113/500000) 335 214
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t55 : ((240838893789/2500000000000 : ℚ) : ℝ) ≤ stT335 55 := by
  have hc : ((178611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240838893789/2500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((178611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c56 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((521821/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2554531/10000000) (δ := 8429/500000000) (ψ := -685113/500000) 335 215
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t56 : ((348589451313/5000000000000 : ℚ) : ℝ) ≤ stT335 56 := by
  have hc : ((521721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348589451313/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((521721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c57 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((24241/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3439079/10000000) (δ := 1047/62500000) (ψ := -685113/500000) 335 216
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t57 : ((16045711781/625000000000 : ℚ) : ℝ) ≤ stT335 57 := by
  have hc : ((48457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16045711781/625000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((48457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c58 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-64697/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -458141/1000000) (δ := 4211/250000000) (ψ := -685113/500000) 335 217
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t58 : ((-8498419293/250000000000 : ℚ) : ℝ) ≤ stT335 58 := by
  have hc : ((-32361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8498419293/250000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-32361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c59 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-146001/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5972813/10000000) (δ := 16767/1000000000) (ψ := -685113/500000) 335 218
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t59 : ((-19010327969/200000000000 : ℚ) : ℝ) ≤ stT335 59 := by
  have hc : ((-146021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19010327969/200000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-146021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c60 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-497519/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760483/1000000) (δ := 8387/500000000) (ψ := -685113/500000) 335 219
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t60 : ((-128471818231/1000000000000 : ℚ) : ℝ) ≤ stT335 60 := by
  have hc : ((-497569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128471818231/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-497569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c61 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-199593/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6238459/10000000) (δ := 8437/500000000) (ψ := -685113/500000) 335 219
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t61 : ((-127792349521/1250000000000 : ℚ) : ℝ) ≤ stT335 61 := by
  have hc : ((-99809/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127792349521/1250000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-99809/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c62 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-88553/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518583/1250000) (δ := 8411/500000000) (ψ := -685113/500000) 335 220
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t62 : ((-56294743653/5000000000000 : ℚ) : ℝ) ≤ stT335 62 := by
  have hc : ((-88653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56294743653/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-88653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c63 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((370441/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 460259/2500000) (δ := 4197/250000000) (ψ := -685113/500000) 335 221
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t63 : ((466648583471/5000000000000 : ℚ) : ℝ) ≤ stT335 63 := by
  have hc : ((370391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466648583471/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((370391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c64 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((963479/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338863/5000000) (δ := 3359/200000000) (ψ := -685113/500000) 335 222
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t64 : ((963379/8000000 : ℚ) : ℝ) ≤ stT335 64 := by
  have hc : ((963379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((963379/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((963379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c65 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((104439/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1700461/5000000) (δ := 21/1250000) (ψ := -685113/500000) 335 223
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t65 : ((129478582983/5000000000000 : ℚ) : ℝ) ≤ stT335 65 := by
  have hc : ((104389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129478582983/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((104389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c66 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-409063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3161177/5000000) (δ := 16793/1000000000) (ψ := -685113/500000) 335 224
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t66 : ((-100716665679/1000000000000 : ℚ) : ℝ) ≤ stT335 66 := by
  have hc : ((-409113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100716665679/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-409113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c67 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-50397/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6271887/10000000) (δ := 16893/1000000000) (ψ := -685113/500000) 335 224
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t67 : ((-49261918807/500000000000 : ℚ) : ℝ) ≤ stT335 67 := by
  have hc : ((-201613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49261918807/500000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-201613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c68 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((372933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 297157/1000000) (δ := 8443/500000000) (ψ := -685113/500000) 335 225
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t68 : ((226063188387/5000000000000 : ℚ) : ℝ) ≤ stT335 68 := by
  have hc : ((372833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226063188387/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((372833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c69 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((122409/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254949/5000000) (δ := 16779/1000000000) (ψ := -685113/500000) 335 226
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t69 : ((147348005697/1250000000000 : ℚ) : ℝ) ≤ stT335 69 := by
  have hc : ((244793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147348005697/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((244793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c70 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-47993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166693/400000) (δ := 4193/250000000) (ψ := -685113/500000) 335 227
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t70 : ((-57422386847/5000000000000 : ℚ) : ℝ) ≤ stT335 70 := by
  have hc : ((-48043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57422386847/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-48043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c71 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-499197/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3856139/5000000) (δ := 16931/1000000000) (ψ := -685113/500000) 335 227
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t71 : ((-296248676577/2500000000000 : ℚ) : ℝ) ≤ stT335 71 := by
  have hc : ((-499247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296248676577/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-499247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c72 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((41781/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3717841/10000000) (δ := 8469/500000000) (ψ := -685113/500000) 335 228
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t72 : ((49180442541/5000000000000 : ℚ) : ℝ) ≤ stT335 72 := by
  have hc : ((41731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49180442541/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((41731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c73 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((39387/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219117/5000000) (δ := 16757/1000000000) (ψ := -685113/500000) 335 229
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t73 : ((46094296413/400000000000 : ℚ) : ℝ) ≤ stT335 73 := by
  have hc : ((39383/40000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46094296413/400000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((39383/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c74 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-16193/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4751507/10000000) (δ := 16853/1000000000) (ψ := -685113/500000) 335 230
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t74 : ((-9414901223/250000000000 : ℚ) : ℝ) ≤ stT335 74 := by
  have hc : ((-8099/25000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9414901223/250000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-8099/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c75 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-85489/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6490339/10000000) (δ := 16753/1000000000) (ψ := -685113/500000) 335 230
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t75 : ((-98725780799/1000000000000 : ℚ) : ℝ) ≤ stT335 75 := by
  have hc : ((-85499/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98725780799/1000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-85499/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c76 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((365813/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1875231/10000000) (δ := 843/50000000) (ψ := -685113/500000) 335 231
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t76 : ((209779345257/2500000000000 : ℚ) : ℝ) ≤ stT335 76 := by
  have hc : ((365763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209779345257/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((365763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c77 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((50611/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2884849/10000000) (δ := 4209/250000000) (ψ := -685113/500000) 335 232
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t77 : ((23064921437/500000000000 : ℚ) : ℝ) ≤ stT335 77 := by
  have hc : ((101197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23064921437/500000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((101197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c78 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-999633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1557243/2000000) (δ := 16929/1000000000) (ψ := -685113/500000) 335 233
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t78 : ((-565987840887/5000000000000 : ℚ) : ℝ) ≤ stT335 78 := by
  have hc : ((-999733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-565987840887/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-999733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c79 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((16227/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1441349/5000000) (δ := 8387/500000000) (ψ := -685113/500000) 335 233
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t79 : ((18252286401/400000000000 : ℚ) : ℝ) ≤ stT335 79 := by
  have hc : ((16223/40000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18252286401/400000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((16223/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c80 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((608833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57263/250000) (δ := 8441/500000000) (ψ := -685113/500000) 335 234
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t80 : ((680583582189/10000000000000 : ℚ) : ℝ) ≤ stT335 80 := by
  have hc : ((608733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680583582189/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((608733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c81 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-15541/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94933/125000) (δ := 8407/500000000) (ψ := -685113/500000) 335 235
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t81 : ((-34539055409/312500000000 : ℚ) : ℝ) ≤ stT335 81 := by
  have hc : ((-248681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34539055409/312500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-248681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c82 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((238909/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2681569/10000000) (δ := 16789/1000000000) (ψ := -685113/500000) 335 235
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t82 : ((52755115317/1000000000000 : ℚ) : ℝ) ≤ stT335 82 := by
  have hc : ((238859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52755115317/1000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((238859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c83 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((408589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1437361/5000000) (δ := 16807/1000000000) (ψ := -685113/500000) 335 236
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t83 : ((224187341469/5000000000000 : ℚ) : ℝ) ≤ stT335 83 := by
  have hc : ((408489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224187341469/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((408489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c84 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-961201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 894413/1250000) (δ := 8399/250000000) (ψ := -685113/500000) 335 236
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t84 : ((-104886590809/1000000000000 : ℚ) : ℝ) ≤ stT335 84 := by
  have hc : ((-961301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104886590809/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-961301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c85 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((213979/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 339673/2500000) (δ := 169/10000000) (ψ := -685113/500000) 335 237
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t85 : ((29008204251/312500000000 : ℚ) : ℝ) ≤ stT335 85 := by
  have hc : ((106977/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29008204251/312500000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((106977/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c86 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-248133/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4553871/10000000) (δ := 16793/1000000000) (ψ := -685113/500000) 335 238
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t86 : ((-33459574303/1250000000000 : ℚ) : ℝ) ≤ stT335 86 := by
  have hc : ((-248233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33459574303/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-248233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c87 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-462273/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5128383/10000000) (δ := 1681/100000000) (ψ := -685113/500000) 335 238
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t87 : ((-495716104149/10000000000000 : ℚ) : ℝ) ≤ stT335 87 := by
  have hc : ((-462373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-495716104149/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-462373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c88 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((919803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252011/2500000) (δ := 16817/1000000000) (ψ := -685113/500000) 335 239
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t88 : ((980406157109/10000000000000 : ℚ) : ℝ) ≤ stT335 88 := by
  have hc : ((919703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((980406157109/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((919703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c89 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-485607/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1813169/2500000) (δ := 673/40000000) (ψ := -685113/500000) 335 240
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t89 : ((-257397724343/2500000000000 : ℚ) : ℝ) ≤ stT335 89 := by
  have hc : ((-485657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257397724343/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-485657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c90 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((665983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2104963/10000000) (δ := 677/40000000) (ψ := -685113/500000) 335 240
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t90 : ((175475485809/2500000000000 : ℚ) : ℝ) ≤ stT335 90 := by
  have hc : ((665883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175475485809/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((665883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c91 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-33581/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4348751/10000000) (δ := 1051/31250000) (ψ := -685113/500000) 335 241
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t91 : ((-7044684857/400000000000 : ℚ) : ℝ) ≤ stT335 91 := by
  have hc : ((-33601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7044684857/400000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-33601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c92 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-10743/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 600541/1250000) (δ := 16771/1000000000) (ψ := -685113/500000) 335 241
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t92 : ((-89628958237/2500000000000 : ℚ) : ℝ) ≤ stT335 92 := by
  have hc : ((-85969/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89628958237/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-85969/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c93 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((369301/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -924753/5000000) (δ := 16939/1000000000) (ψ := -685113/500000) 335 242
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t93 : ((382895193701/5000000000000 : ℚ) : ℝ) ≤ stT335 93 := by
  have hc : ((369251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((382895193701/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((369251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c94 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-238947/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7107807/10000000) (δ := 527/31250000) (ψ := -685113/500000) 335 242
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t94 : ((-30810122273/312500000000 : ℚ) : ℝ) ≤ stT335 94 := by
  have hc : ((-59743/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30810122273/312500000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-59743/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c95 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((994499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262353/10000000) (δ := 8423/500000000) (ψ := -685113/500000) 335 243
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t95 : ((510115748611/5000000000000 : ℚ) : ℝ) ≤ stT335 95 := by
  have hc : ((994399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((510115748611/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((994399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c96 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-891009/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6675897/10000000) (δ := 337/20000000) (ψ := -685113/500000) 335 244
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t96 : ((-909484558689/10000000000000 : ℚ) : ℝ) ≤ stT335 96 := by
  have hc : ((-891109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-909484558689/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-891109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c97 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((34793/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 500737/2500000) (δ := 337/20000000) (ψ := -685113/500000) 335 244
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t97 : ((4415232081/62500000000 : ℚ) : ℝ) ≤ stT335 97 := by
  have hc : ((8697/12500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4415232081/62500000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((8697/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c98 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-457589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1278799/2500000) (δ := 843/50000000) (ψ := -685113/500000) 335 245
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t98 : ((-462335916417/10000000000000 : ℚ) : ℝ) ≤ stT335 98 := by
  have hc : ((-457689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-462335916417/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-457689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c99 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((214149/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3387439/10000000) (δ := 843/50000000) (ψ := -685113/500000) 335 245
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t99 : ((215127164813/10000000000000 : ℚ) : ℝ) ≤ stT335 99 := by
  have hc : ((214049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215127164813/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((214049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c100 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((9437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1951699/5000000) (δ := 4217/250000000) (ψ := -685113/500000) 335 246
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t100 : ((9336990663/10000000000000 : ℚ) : ℝ) ≤ stT335 100 := by
  have hc : ((9337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9336990663/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((9337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c101 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-199873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2215031/5000000) (δ := 4217/250000000) (ψ := -685113/500000) 335 246
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t101 : ((-99490366987/5000000000000 : ℚ) : ℝ) ≤ stT335 101 := by
  have hc : ((-199973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99490366987/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-199973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c102 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((352421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15133/50000) (δ := 27/1600000) (ψ := -685113/500000) 335 247
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t102 : ((348849581187/10000000000000 : ℚ) : ℝ) ≤ stT335 102 := by
  have hc : ((352321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348849581187/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((352321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c103 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-9357/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5144133/10000000) (δ := 529/31250000) (ψ := -685113/500000) 335 247
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t103 : ((-922170347/20000000000 : ℚ) : ℝ) ≤ stT335 103 := by
  have hc : ((-9359/20000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-922170347/20000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-9359/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c104 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((8589/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2471989/10000000) (δ := 16921/1000000000) (ψ := -685113/500000) 335 248
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t104 : ((6736535571/125000000000 : ℚ) : ℝ) ≤ stT335 104 := by
  have hc : ((137399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6736535571/125000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((137399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c105 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-12043/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1385617/2500000) (δ := 8441/500000000) (ψ := -685113/500000) 335 248
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t105 : ((-2350945509/40000000000 : ℚ) : ℝ) ≤ stT335 105 := by
  have hc : ((-2409/4000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2350945509/40000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-2409/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c106 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((157191/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -556771/2500000) (δ := 16889/1000000000) (ψ := -685113/500000) 335 249
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t106 : ((15265297831/250000000000 : ℚ) : ℝ) ≤ stT335 106 := by
  have hc : ((78583/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15265297831/250000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((78583/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c107 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-315931/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5636873/10000000) (δ := 8407/500000000) (ψ := -685113/500000) 335 249
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t107 : ((-305470523997/5000000000000 : ℚ) : ℝ) ≤ stT335 107 := by
  have hc : ((-315981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305470523997/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-315981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c108 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((612061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228033/1000000) (δ := 4199/250000000) (ψ := -685113/500000) 335 250
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t108 : ((2355437889/40000000000 : ℚ) : ℝ) ≤ stT335 108 := by
  have hc : ((611961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2355437889/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((611961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c109 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-28423/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1359643/2500000) (δ := 16907/1000000000) (ψ := -685113/500000) 335 250
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t109 : ((-6807276489/125000000000 : ℚ) : ℝ) ≤ stT335 109 := by
  have hc : ((-7107/12500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6807276489/125000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-7107/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c110 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((99797/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1310461/5000000) (δ := 4201/250000000) (ψ := -685113/500000) 335 251
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t110 : ((47566788987/1000000000000 : ℚ) : ℝ) ≤ stT335 110 := by
  have hc : ((99777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47566788987/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((99777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c111 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-100237/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4958369/10000000) (δ := 16799/1000000000) (ψ := -685113/500000) 335 251
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t111 : ((-23791119849/625000000000 : ℚ) : ℝ) ≤ stT335 111 := by
  have hc : ((-50131/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23791119849/625000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-50131/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c112 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((27197/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404799/1250000) (δ := 4223/250000000) (ψ := -685113/500000) 335 252
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t112 : ((25689295357/1000000000000 : ℚ) : ℝ) ≤ stT335 112 := by
  have hc : ((27187/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25689295357/1000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((27187/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c113 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-11143/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2103073/5000000) (δ := 16811/1000000000) (ψ := -685113/500000) 335 252
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t113 : ((-10491861313/1000000000000 : ℚ) : ℝ) ≤ stT335 113 := by
  have hc : ((-11153/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10491861313/1000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-11153/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c114 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-78299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206147/500000) (δ := 3357/200000000) (ψ := -685113/500000) 335 253
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t114 : ((-36713702907/5000000000000 : ℚ) : ℝ) ≤ stT335 114 := by
  have hc : ((-78399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36713702907/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-78399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c115 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((144979/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1595767/5000000) (δ := 8409/500000000) (ψ := -685113/500000) 335 253
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t115 : ((16893359027/625000000000 : ℚ) : ℝ) ≤ stT335 115 := by
  have hc : ((144929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16893359027/625000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((144929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c116 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-255069/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2632677/5000000) (δ := 677/40000000) (ψ := -685113/500000) 335 254
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t116 : ((-236872123763/5000000000000 : ℚ) : ℝ) ≤ stT335 116 := by
  have hc : ((-255119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236872123763/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-255119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c117 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((718307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 961789/5000000) (δ := 8389/500000000) (ψ := -685113/500000) 335 254
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t117 : ((1327964743/20000000000 : ℚ) : ℝ) ≤ stT335 117 := by
  have hc : ((718207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1327964743/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((718207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c118 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-221873/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3328337/5000000) (δ := 16771/1000000000) (ψ := -685113/500000) 335 255
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t118 : ((-4085475027/50000000000 : ℚ) : ℝ) ≤ stT335 118 := by
  have hc : ((-110949/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4085475027/50000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-110949/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c119 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((30829/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410821/10000000) (δ := 16771/1000000000) (ψ := -685113/500000) 335 255
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t119 : ((113032071843/1250000000000 : ℚ) : ℝ) ≤ stT335 119 := by
  have hc : ((246607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113032071843/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((246607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c120 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-24623/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927409/1250000) (δ := 16871/1000000000) (ψ := -685113/500000) 335 255
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t120 : ((-44959809621/500000000000 : ℚ) : ℝ) ≤ stT335 120 := by
  have hc : ((-49251/50000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44959809621/500000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-49251/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c121 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((215019/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669223/5000000) (δ := 4191/250000000) (ψ := -685113/500000) 335 256
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t121 : ((9772444773/125000000000 : ℚ) : ℝ) ≤ stT335 121 := by
  have hc : ((107497/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9772444773/125000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((107497/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c122 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-9469/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2777299/5000000) (δ := 16839/1000000000) (ψ := -685113/500000) 335 256
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t122 : ((-68593996191/1250000000000 : ℚ) : ℝ) ≤ stT335 122 := by
  have hc : ((-151529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68593996191/1250000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-151529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c123 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((241737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1658301/5000000) (δ := 2107/125000000) (ψ := -685113/500000) 335 257
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t123 : ((217876592153/10000000000000 : ℚ) : ℝ) ≤ stT335 123 := by
  have hc : ((241637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217876592153/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((241637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c124 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((11489/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3464803/10000000) (δ := 2107/125000000) (ψ := -685113/500000) 335 257
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t124 : ((20623616103/1250000000000 : ℚ) : ℝ) ≤ stT335 124 := by
  have hc : ((45931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20623616103/1250000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((45931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c125 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-296863/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5516193/10000000) (δ := 16949/1000000000) (ψ := -685113/500000) 335 258
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t125 : ((-66391825191/1250000000000 : ℚ) : ℝ) ≤ stT335 125 := by
  have hc : ((-296913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66391825191/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-296913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c126 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((35791/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46287/400000) (δ := 8377/500000000) (ψ := -685113/500000) 335 258
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t126 : ((3188156469/40000000000 : ℚ) : ℝ) ≤ stT335 126 := by
  have hc : ((35787/40000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3188156469/40000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((35787/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c127 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-499767/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243053/312500) (δ := 16849/1000000000) (ψ := -685113/500000) 335 258
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t127 : ((-443516113669/5000000000000 : ℚ) : ℝ) ≤ stT335 127 := by
  have hc : ((-499817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-443516113669/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-499817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c128 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((855317/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1361587/10000000) (δ := 16761/1000000000) (ψ := -685113/500000) 335 259
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t128 : ((755911767611/10000000000000 : ℚ) : ℝ) ≤ stT335 128 := by
  have hc : ((855217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((755911767611/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((855217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c129 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-236021/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1031201/2000000) (δ := 8471/500000000) (ψ := -685113/500000) 335 259
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t129 : ((-207848948021/5000000000000 : ℚ) : ℝ) ≤ stT335 129 := by
  have hc : ((-236071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207848948021/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-236071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c130 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-2523/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4084783/10000000) (δ := 3367/200000000) (ψ := -685113/500000) 335 260
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t130 : ((-2216328093/400000000000 : ℚ) : ℝ) ≤ stT335 130 := by
  have hc : ((-2527/40000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2216328093/400000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-2527/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c131 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((595299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72903/312500) (δ := 131/7812500) (ψ := -685113/500000) 335 260
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t131 : ((65003468387/1250000000000 : ℚ) : ℝ) ≤ stT335 131 := by
  have hc : ((595199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65003468387/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((595199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c132 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-235763/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1401243/2000000) (δ := 4207/250000000) (ψ := -685113/500000) 335 261
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t132 : ((-51306820383/625000000000 : ℚ) : ℝ) ≤ stT335 132 := by
  have hc : ((-58947/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51306820383/625000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-58947/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c133 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((962649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137087/2000000) (δ := 4207/250000000) (ψ := -685113/500000) 335 261
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t133 : ((834634900841/10000000000000 : ℚ) : ℝ) ≤ stT335 133 := by
  have hc : ((962549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((834634900841/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((962549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c134 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-123317/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1117597/2000000) (δ := 1347/40000000) (ψ := -685113/500000) 335 261
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t134 : ((-106547010853/2000000000000 : ℚ) : ℝ) ≤ stT335 134 := by
  have hc : ((-123337/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106547010853/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-123337/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c135 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((13513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486651/1250000) (δ := 16783/1000000000) (ψ := -685113/500000) 335 262
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t135 : ((5772029703/5000000000000 : ℚ) : ℝ) ≤ stT335 135 := by
  have hc : ((13413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5772029703/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((13413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c136 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((609751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1143813/5000000) (δ := 16883/1000000000) (ψ := -685113/500000) 335 262
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t136 : ((130692713823/2500000000000 : ℚ) : ℝ) ≤ stT335 136 := by
  have hc : ((609651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130692713823/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((609651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c137 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-243547/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7284729/10000000) (δ := 16813/1000000000) (ψ := -685113/500000) 335 263
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t137 : ((-26012210847/312500000000 : ℚ) : ℝ) ≤ stT335 137 := by
  have hc : ((-60893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26012210847/312500000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-60893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c138 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((88813/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1193843/10000000) (δ := 16913/1000000000) (ψ := -685113/500000) 335 263
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t138 : ((9449260821/125000000000 : ℚ) : ℝ) ≤ stT335 138 := by
  have hc : ((88803/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9449260821/125000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((88803/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c139 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-362051/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4853159/10000000) (δ := 1689/100000000) (ψ := -685113/500000) 335 263
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t139 : ((-307172494539/10000000000000 : ℚ) : ℝ) ≤ stT335 139 := by
  have hc : ((-362151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307172494539/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-362151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c140 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-72263/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2425593/5000000) (δ := 8403/500000000) (ψ := -685113/500000) 335 264
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t140 : ((-12218067773/400000000000 : ℚ) : ℝ) ≤ stT335 140 := by
  have hc : ((-72283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12218067773/400000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-72283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c141 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((903103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1109637/10000000) (δ := 16897/1000000000) (ψ := -685113/500000) 335 264
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t141 : ((760464879453/10000000000000 : ℚ) : ℝ) ≤ stT335 141 := by
  have hc : ((903003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760464879453/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((903003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c142 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-945969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7028417/10000000) (δ := 16897/1000000000) (ψ := -685113/500000) 335 264
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t142 : ((-396962037779/5000000000000 : ℚ) : ℝ) ≤ stT335 142 := by
  have hc : ((-946069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-396962037779/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-946069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c143 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((108713/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2802307/10000000) (δ := 16899/1000000000) (ψ := -685113/500000) 335 265
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t143 : ((2840295953/78125000000 : ℚ) : ℝ) ≤ stT335 143 := by
  have hc : ((6793/15625 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2840295953/78125000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((6793/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c144 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((43711/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 379237/1250000) (δ := 4201/250000000) (ψ := -685113/500000) 335 265
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t144 : ((72830804201/2500000000000 : ℚ) : ℝ) ≤ stT335 144 := by
  have hc : ((87397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72830804201/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((87397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c145 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-462391/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6878149/10000000) (δ := 4223/250000000) (ψ := -685113/500000) 335 266
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t145 : ((-76807288131/1000000000000 : ℚ) : ℝ) ≤ stT335 145 := by
  have hc : ((-462441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76807288131/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-462441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c146 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((112619/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224419/2000000) (δ := 2099/125000000) (ψ := -685113/500000) 335 266
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t146 : ((37277480973/500000000000 : ℚ) : ℝ) ≤ stT335 146 := by
  have hc : ((225213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37277480973/500000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((225213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c147 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-6597/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1148649/2500000) (δ := 4223/250000000) (ψ := -685113/500000) 335 266
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t147 : ((-10886363613/500000000000 : ℚ) : ℝ) ≤ stT335 147 := by
  have hc : ((-13199/50000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10886363613/500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-13199/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c148 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-113481/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -679421/1250000) (δ := 8409/500000000) (ψ := -685113/500000) 335 267
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t148 : ((-18659450899/400000000000 : ℚ) : ℝ) ≤ stT335 148 := by
  have hc : ((-113501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18659450899/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-113501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c149 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((498329/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 204441/10000000) (δ := 8459/500000000) (ψ := -685113/500000) 335 267
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t149 : ((408205603449/5000000000000 : ℚ) : ℝ) ≤ stT335 149 := by
  have hc : ((498279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408205603449/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((498279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c150 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-341463/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2903197/5000000) (δ := 3377/200000000) (ψ := -685113/500000) 335 267
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t150 : ((-278844339961/5000000000000 : ℚ) : ℝ) ≤ stT335 150 := by
  have hc : ((-341513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278844339961/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-341513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c151 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-163157/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1084179/2500000) (δ := 8463/500000000) (ψ := -685113/500000) 335 268
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t151 : ((-132856750773/10000000000000 : ℚ) : ℝ) ≤ stT335 151 := by
  have hc : ((-163257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132856750773/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-163257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c152 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((111073/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119137/1000000) (δ := 8413/500000000) (ψ := -685113/500000) 335 268
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t152 : ((180163897947/2500000000000 : ℚ) : ℝ) ≤ stT335 152 := by
  have hc : ((222121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180163897947/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((222121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c153 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-89233/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835399/1250000) (δ := 16877/1000000000) (ψ := -685113/500000) 335 268
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t153 : ((-72148771079/1000000000000 : ℚ) : ℝ) ≤ stT335 153 := by
  have hc : ((-89243/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72148771079/1000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-89243/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c154 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((71411/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -356871/1000000) (δ := 1687/100000000) (ψ := -685113/500000) 335 269
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t154 : ((28752131871/2500000000000 : ℚ) : ℝ) ≤ stT335 154 := by
  have hc : ((71361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28752131871/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((71361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c155 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((368963/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1852009/10000000) (δ := 1677/100000000) (ψ := -685113/500000) 335 269
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t155 : ((296317930947/5000000000000 : ℚ) : ℝ) ≤ stT335 155 := by
  have hc : ((368913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296317930947/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((368913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c156 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-242447/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56546/78125) (δ := 16833/1000000000) (ψ := -685113/500000) 335 269
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t156 : ((-24266628069/312500000000 : ℚ) : ℝ) ≤ stT335 156 := by
  have hc : ((-30309/31250 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24266628069/312500000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-30309/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c157 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((19859/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1559309/5000000) (δ := 16763/1000000000) (ψ := -685113/500000) 335 270
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t157 : ((31688403673/1250000000000 : ℚ) : ℝ) ≤ stT335 157 := by
  have hc : ((79411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31688403673/1250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((79411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c158 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((63751/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2198837/10000000) (δ := 16763/1000000000) (ψ := -685113/500000) 335 270
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t158 : ((50709598737/1000000000000 : ℚ) : ℝ) ≤ stT335 158 := by
  have hc : ((63741/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50709598737/1000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((63741/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c159 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-494499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 935349/1250000) (δ := 16763/1000000000) (ψ := -685113/500000) 335 270
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t159 : ((-98050768387/1250000000000 : ℚ) : ℝ) ≤ stT335 159 := by
  have hc : ((-494549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98050768387/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-494549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c160 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((37189/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2974381/10000000) (δ := 16847/1000000000) (ψ := -685113/500000) 335 271
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t160 : ((29392564851/1000000000000 : ℚ) : ℝ) ≤ stT335 160 := by
  have hc : ((37179/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29392564851/1000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((37179/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c161 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((311797/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2243663/10000000) (δ := 16947/1000000000) (ψ := -685113/500000) 335 271
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t161 : ((24569092817/500000000000 : ℚ) : ℝ) ≤ stT335 161 := by
  have hc : ((311747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24569092817/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((311747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c162 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-985617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7429463/10000000) (δ := 16947/1000000000) (ψ := -685113/500000) 335 271
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t162 : ((-30978128159/400000000000 : ℚ) : ℝ) ≤ stT335 162 := by
  have hc : ((-985717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30978128159/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-985717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c163 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((31547/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -312461/1000000) (δ := 16949/1000000000) (ψ := -685113/500000) 335 272
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t163 : ((1235083531/50000000000 : ℚ) : ℝ) ≤ stT335 163 := by
  have hc : ((31537/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1235083531/50000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((31537/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c164 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((174341/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 499427/2500000) (δ := 8377/500000000) (ψ := -685113/500000) 335 272
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t164 : ((8507361643/156250000000 : ℚ) : ℝ) ≤ stT335 164 := by
  have hc : ((43579/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8507361643/156250000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((43579/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c165 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-953533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 708887/1000000) (δ := 16949/1000000000) (ψ := -685113/500000) 335 272
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t165 : ((-742402336867/10000000000000 : ℚ) : ℝ) ≤ stT335 165 := by
  have hc : ((-953633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-742402336867/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-953633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c166 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((146797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3558667/10000000) (δ := 16941/1000000000) (ψ := -685113/500000) 335 273
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t166 : ((2277177531/200000000000 : ℚ) : ℝ) ≤ stT335 166 := by
  have hc : ((146697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2277177531/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((146697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c167 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((207933/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 735721/5000000) (δ := 16841/1000000000) (ψ := -685113/500000) 335 273
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t167 : ((40220998071/625000000000 : ℚ) : ℝ) ≤ stT335 167 := by
  have hc : ((51977/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40220998071/625000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((51977/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c168 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-106367/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6471401/10000000) (δ := 8381/500000000) (ψ := -685113/500000) 335 273
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t168 : ((-164147185403/2500000000000 : ℚ) : ℝ) ≤ stT335 168 := by
  have hc : ((-212759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164147185403/2500000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-212759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c169 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-27051/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4266167/10000000) (δ := 16869/1000000000) (ψ := -685113/500000) 335 274
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t169 : ((-20823852401/2000000000000 : ℚ) : ℝ) ≤ stT335 169 := by
  have hc : ((-27071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20823852401/2000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-27071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c170 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((963789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 674831/10000000) (δ := 8467/500000000) (ψ := -685113/500000) 335 274
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t170 : ((184778692549/2500000000000 : ℚ) : ℝ) ≤ stT335 170 := by
  have hc : ((963689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184778692549/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((963689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c171 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-154057/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5586853/10000000) (δ := 16869/1000000000) (ψ := -685113/500000) 335 274
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t171 : ((-736434919/15625000000 : ℚ) : ℝ) ≤ stT335 171 := by
  have hc : ((-77041/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-736434919/15625000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-77041/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c172 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-125151/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1309433/2500000) (δ := 16827/1000000000) (ψ := -685113/500000) 335 275
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t172 : ((-11930727971/312500000000 : ℚ) : ℝ) ≤ stT335 172 := by
  have hc : ((-15647/31250 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11930727971/312500000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-15647/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c173 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((247077/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382661/10000000) (δ := 16927/1000000000) (ψ := -685113/500000) 335 275
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t173 : ((9391496491/125000000000 : ℚ) : ℝ) ≤ stT335 173 := by
  have hc : ((61763/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9391496491/125000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((61763/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c174 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-3211/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2222219/5000000) (δ := 16827/1000000000) (ψ := -685113/500000) 335 275
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t174 : ((-38967046699/2500000000000 : ℚ) : ℝ) ≤ stT335 174 := by
  have hc : ((-51401/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38967046699/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-51401/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c175 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-84939/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101001/156250) (δ := 841/50000000) (ψ := -685113/500000) 335 276
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t175 : ((-64215412621/1000000000000 : ℚ) : ℝ) ≤ stT335 175 := by
  have hc : ((-84949/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64215412621/1000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-84949/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c176 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((12181/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1691989/10000000) (δ := 841/50000000) (ψ := -685113/500000) 335 276
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t176 : ((73444736319/1250000000000 : ℚ) : ℝ) ≤ stT335 176 := by
  have hc : ((194871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73444736319/1250000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((194871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c177 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((171237/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3053119/10000000) (δ := 16883/1000000000) (ψ := -685113/500000) 335 276
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t177 : ((64336011901/2500000000000 : ℚ) : ℝ) ≤ stT335 177 := by
  have hc : ((171187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64336011901/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((171187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c178 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-199891/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3885713/5000000) (δ := 841/50000000) (ψ := -685113/500000) 335 276
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t178 : ((-37459922913/500000000000 : ℚ) : ℝ) ≤ stT335 178 := by
  have hc : ((-199911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37459922913/500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-199911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c179 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((10783/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3244611/10000000) (δ := 16813/1000000000) (ψ := -685113/500000) 335 277
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t179 : ((1611320373/80000000000 : ℚ) : ℝ) ≤ stT335 179 := by
  have hc : ((10779/40000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1611320373/80000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((10779/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c180 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((842741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 710551/5000000) (δ := 1689/100000000) (ψ := -685113/500000) 335 277
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t180 : ((125613336511/2000000000000 : ℚ) : ℝ) ≤ stT335 180 := by
  have hc : ((842641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125613336511/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((842641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c181 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-753659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6061019/10000000) (δ := 16813/1000000000) (ψ := -685113/500000) 335 277
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t181 : ((-112053059181/2000000000000 : ℚ) : ℝ) ≤ stT335 181 := by
  have hc : ((-753759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112053059181/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-753759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c182 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-106997/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2516327/5000000) (δ := 16797/1000000000) (ψ := -685113/500000) 335 278
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t182 : ((-31732023/1000000000 : ℚ) : ℝ) ≤ stT335 182 := by
  have hc : ((-53511/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31732023/1000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-53511/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c183 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((984301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -443573/10000000) (δ := 8403/500000000) (ψ := -685113/500000) 335 278
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t183 : ((727542047421/10000000000000 : ℚ) : ℝ) ≤ stT335 183 := by
  have hc : ((984201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((727542047421/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((984201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c184 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-77313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4120467/10000000) (δ := 8403/500000000) (ψ := -685113/500000) 335 278
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t184 : ((-5706963773/1000000000000 : ℚ) : ℝ) ≤ stT335 184 := by
  have hc : ((-77413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5706963773/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-77413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c185 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-948501/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3524081/5000000) (δ := 3381/200000000) (ψ := -685113/500000) 335 279
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t185 : ((-139485136843/2000000000000 : ℚ) : ℝ) ≤ stT335 185 := by
  have hc : ((-948601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139485136843/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-948601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c186 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((8266/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2533367/10000000) (δ := 3381/200000000) (ψ := -685113/500000) 335 279
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t186 : ((19391279457/500000000000 : ℚ) : ℝ) ≤ stT335 186 := by
  have hc : ((132231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19391279457/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((132231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c187 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((141771/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489327/2500000) (δ := 3381/200000000) (ψ := -685113/500000) 335 279
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t187 : ((12957317159/250000000000 : ℚ) : ℝ) ≤ stT335 187 := by
  have hc : ((141751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12957317159/250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((141751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c188 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-210203/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3211973/5000000) (δ := 8449/500000000) (ψ := -685113/500000) 335 279
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t188 : ((-1533245361/25000000000 : ℚ) : ℝ) ≤ stT335 188 := by
  have hc : ((-52557/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1533245361/25000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-52557/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c189 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-44689/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1210249/2500000) (δ := 16891/1000000000) (ψ := -685113/500000) 335 280
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t189 : ((-65031116379/2500000000000 : ℚ) : ℝ) ≤ stT335 189 := by
  have hc : ((-89403/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65031116379/2500000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-89403/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c190 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((49291/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105377/2500000) (δ := 4203/250000000) (ψ := -685113/500000) 335 280
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t190 : ((4469476267/62500000000 : ℚ) : ℝ) ≤ stT335 190 := by
  have hc : ((24643/25000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4469476267/62500000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((24643/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c191 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-4787/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248429/625000) (δ := 16891/1000000000) (ψ := -685113/500000) 335 280
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t191 : ((-34818429/25000000000 : ℚ) : ℝ) ≤ stT335 191 := by
  have hc : ((-1203/62500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34818429/25000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-1203/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c192 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-980523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3679879/5000000) (δ := 4221/250000000) (ψ := -685113/500000) 335 281
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t192 : ((-88462981453/1250000000000 : ℚ) : ℝ) ≤ stT335 192 := by
  have hc : ((-980623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88462981453/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-980623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c193 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((179479/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3009113/10000000) (δ := 4221/250000000) (ψ := -685113/500000) 335 281
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t193 : ((25831137127/1000000000000 : ℚ) : ℝ) ≤ stT335 193 := by
  have hc : ((179429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25831137127/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((179429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c194 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((108/125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1319087/10000000) (δ := 4221/250000000) (ψ := -685113/500000) 335 281
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t194 : ((3101219581/50000000000 : ℚ) : ℝ) ≤ stT335 194 := by
  have hc : ((8639/10000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3101219581/50000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((8639/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c195 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-628177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 562501/1000000) (δ := 16819/1000000000) (ψ := -685113/500000) 335 281
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t195 : ((-89983716771/2000000000000 : ℚ) : ℝ) ≤ stT335 195 := by
  have hc : ((-628277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89983716771/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-628277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c196 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-34039/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5799057/10000000) (δ := 8413/500000000) (ψ := -685113/500000) 335 282
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t196 : ((-3039644073/62500000000 : ℚ) : ℝ) ≤ stT335 196 := by
  have hc : ((-8511/12500 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3039644073/62500000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-8511/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c197 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((102113/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192117/1250000) (δ := 16777/1000000000) (ψ := -685113/500000) 335 282
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t197 : ((14548708647/250000000000 : ℚ) : ℝ) ≤ stT335 197 := by
  have hc : ((204201/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14548708647/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((204201/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c198 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((235033/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1351789/5000000) (δ := 8413/500000000) (ψ := -685113/500000) 335 282
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t198 : ((166995133627/5000000000000 : ℚ) : ℝ) ≤ stT335 198 := by
  have hc : ((234983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166995133627/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((234983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c199 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-931421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1384547/2000000) (δ := 16877/1000000000) (ψ := -685113/500000) 335 282
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t199 : ((-330169234761/5000000000000 : ℚ) : ℝ) ≤ stT335 199 := by
  have hc : ((-931521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330169234761/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-931521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c200 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-32631/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4587259/10000000) (δ := 16833/1000000000) (ψ := -685113/500000) 335 283
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t200 : ((-46164894709/2500000000000 : ℚ) : ℝ) ≤ stT335 200 := by
  have hc : ((-65287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46164894709/2500000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-65287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c201 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((986573/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12817/312500) (δ := 16833/1000000000) (ψ := -685113/500000) 335 283
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t201 : ((139160759637/2000000000000 : ℚ) : ℝ) ≤ stT335 201 := by
  have hc : ((986473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139160759637/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((986473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c202 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((36143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3746117/10000000) (δ := 1677/100000000) (ψ := -685113/500000) 335 283
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t202 : ((25394926521/5000000000000 : ℚ) : ℝ) ≤ stT335 202 := by
  have hc : ((36093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25394926521/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((36093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c203 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-999937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -391301/500000) (δ := 8381/500000000) (ψ := -685113/500000) 335 284
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t203 : ((-701888968931/10000000000000 : ℚ) : ℝ) ≤ stT335 203 := by
  have hc : ((-1000037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-701888968931/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-1000037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c204 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((8647/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742109/2000000) (δ := 8381/500000000) (ψ := -685113/500000) 335 284
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t204 : ((302355459/50000000000 : ℚ) : ℝ) ≤ stT335 204 := by
  have hc : ((8637/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302355459/50000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((8637/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c205 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((61761/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38483/1000000) (δ := 8381/500000000) (ψ := -685113/500000) 335 284
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t205 : ((17252548017/250000000000 : ℚ) : ℝ) ≤ stT335 205 := by
  have hc : ((247019/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17252548017/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((247019/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c206 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-211699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4460273/10000000) (δ := 16941/1000000000) (ψ := -685113/500000) 335 284
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t206 : ((-73783782233/5000000000000 : ℚ) : ℝ) ≤ stT335 206 := by
  have hc : ((-211799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73783782233/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-211799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c207 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-241287/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7192013/10000000) (δ := 1053/62500000) (ψ := -685113/500000) 335 285
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t207 : ((-5241364509/78125000000 : ℚ) : ℝ) ≤ stT335 207 := by
  have hc : ((-15082/15625 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5241364509/78125000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-15082/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c208 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((303589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3155849/10000000) (δ := 4237/250000000) (ψ := -685113/500000) 335 285
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t208 : ((1683453483/80000000000 : ℚ) : ℝ) ≤ stT335 208 := by
  have hc : ((303489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1683453483/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((303489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c209 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((941283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107621/1250000) (δ := 3351/200000000) (ψ := -685113/500000) 335 285
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t209 : ((325514728831/5000000000000 : ℚ) : ℝ) ≤ stT335 209 := by
  have hc : ((941183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325514728831/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((941183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c210 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-182041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4858607/10000000) (δ := 1053/62500000) (ψ := -685113/500000) 335 285
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t210 : ((-62827404003/2500000000000 : ℚ) : ℝ) ≤ stT335 210 := by
  have hc : ((-182091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62827404003/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-182091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c211 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-923649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6870729/10000000) (δ := 3351/200000000) (ψ := -685113/500000) 335 286
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t211 : ((-635935600321/10000000000000 : ℚ) : ℝ) ≤ stT335 211 := by
  have hc : ((-923749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-635935600321/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-923749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c212 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((197661/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -582189/2000000) (δ := 3371/200000000) (ψ := -685113/500000) 335 286
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t212 : ((67859815011/2500000000000 : ℚ) : ℝ) ≤ stT335 212 := by
  have hc : ((197611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67859815011/2500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((197611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c213 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((458141/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 515123/5000000) (δ := 3351/200000000) (ψ := -685113/500000) 335 286
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t213 : ((78469614027/1250000000000 : ℚ) : ℝ) ≤ stT335 213 := by
  have hc : ((458091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78469614027/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((458091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c214 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-49873/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1238253/2500000) (δ := 1053/62500000) (ψ := -685113/500000) 335 286
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t214 : ((-34101029403/1250000000000 : ℚ) : ℝ) ≤ stT335 214 := by
  have hc : ((-99771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34101029403/1250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-99771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c215 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-460261/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3425263/5000000) (δ := 8381/500000000) (ψ := -685113/500000) 335 287
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t215 : ((-62785960089/1000000000000 : ℚ) : ℝ) ≤ stT335 215 := by
  have hc : ((-460311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62785960089/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-460311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c216 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((37567/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2964191/10000000) (δ := 8381/500000000) (ψ := -685113/500000) 335 287
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t216 : ((25554271041/1000000000000 : ℚ) : ℝ) ≤ stT335 216 := by
  have hc : ((37557/100000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25554271041/1000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((37557/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c217 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((58457/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452069/5000000) (δ := 8431/500000000) (ψ := -685113/500000) 335 287
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t217 : ((39678940933/625000000000 : ℚ) : ℝ) ≤ stT335 217 := by
  have hc : ((233803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39678940933/625000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((233803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c218 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-20317/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4754711/10000000) (δ := 16941/1000000000) (ψ := -685113/500000) 335 287
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t218 : ((-27529305399/1250000000000 : ℚ) : ℝ) ≤ stT335 218 := by
  have hc : ((-81293/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27529305399/1250000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-81293/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c219 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-957241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3560133/5000000) (δ := 8467/500000000) (ψ := -685113/500000) 335 288
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t219 : ((-323455846329/5000000000000 : ℚ) : ℝ) ≤ stT335 219 := by
  have hc : ((-957341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323455846329/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-957341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c220 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((123161/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3304783/10000000) (δ := 16769/1000000000) (ψ := -685113/500000) 335 288
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t220 : ((83001313089/5000000000000 : ℚ) : ℝ) ≤ stT335 220 := by
  have hc : ((123111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83001313089/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((123111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c221 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((122573/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 493447/10000000) (δ := 16769/1000000000) (ψ := -685113/500000) 335 288
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t221 : ((5152688541/78125000000 : ℚ) : ℝ) ≤ stT335 221 := by
  have hc : ((245121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5152688541/78125000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((245121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c222 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-69263/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534303/1250000) (δ := 8467/500000000) (ψ := -685113/500000) 335 288
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t222 : ((-46519905141/5000000000000 : ℚ) : ℝ) ≤ stT335 222 := by
  have hc : ((-69313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46519905141/5000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-69313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c223 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-498639/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7669479/10000000) (δ := 16827/1000000000) (ψ := -685113/500000) 335 289
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t223 : ((-6678941777/100000000000 : ℚ) : ℝ) ≤ stT335 223 := by
  have hc : ((-498689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6678941777/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-498689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c224 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((379/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3922253/10000000) (δ := 16927/1000000000) (ψ := -685113/500000) 335 289
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t224 : ((239866927/2000000000000 : ℚ) : ℝ) ≤ stT335 224 := by
  have hc : ((359/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239866927/2000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((359/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c225 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((498531/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -191693/10000000) (δ := 16927/1000000000) (ψ := -685113/500000) 335 289
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t225 : ((166160167173/2500000000000 : ℚ) : ℝ) ≤ stT335 225 := by
  have hc : ((498481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166160167173/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((498481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c226 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((161193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3522243/10000000) (δ := 33527/1000000000) (ψ := -685113/500000) 335 289
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t226 : ((10715745267/1000000000000 : ℚ) : ℝ) ≤ stT335 226 := by
  have hc : ((161093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10715745267/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((161093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c227 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-484001/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7219847/10000000) (δ := 16927/1000000000) (ψ := -685113/500000) 335 289
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t227 : ((-80319066481/1250000000000 : ℚ) : ℝ) ≤ stT335 227 := by
  have hc : ((-484051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80319066481/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-484051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c228 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-68941/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4806801/10000000) (δ := 16819/1000000000) (ψ := -685113/500000) 335 290
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t228 : ((-45670594587/2000000000000 : ℚ) : ℝ) ≤ stT335 228 := by
  have hc : ((-68961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45670594587/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-68961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c229 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((179509/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570783/5000000) (δ := 16819/1000000000) (ψ := -685113/500000) 335 290
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t229 : ((59304781001/1000000000000 : ℚ) : ℝ) ≤ stT335 229 := by
  have hc : ((179489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59304781001/1000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((179489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c230 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((537717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2507673/10000000) (δ := 1049/62500000) (ψ := -685113/500000) 335 290
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t230 : ((17724694873/500000000000 : ℚ) : ℝ) ≤ stT335 230 := by
  have hc : ((537617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17724694873/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((537617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c231 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-387159/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6141083/10000000) (δ := 1049/62500000) (ψ := -685113/500000) 335 290
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t231 : ((-7961404249/156250000000 : ℚ) : ℝ) ≤ stT335 231 := by
  have hc : ((-387209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7961404249/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-387209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c232 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-723521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1189843/2000000) (δ := 16891/1000000000) (ψ := -685113/500000) 335 291
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t232 : ((-475081065993/10000000000000 : ℚ) : ℝ) ≤ stT335 232 := by
  have hc : ((-723621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475081065993/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-723621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c233 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((295371/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -586761/2500000) (δ := 16791/1000000000) (ψ := -685113/500000) 335 291
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t233 : ((193470988841/5000000000000 : ℚ) : ℝ) ≤ stT335 233 := by
  have hc : ((295321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193470988841/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((295321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c234 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((879547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239717/10000000) (δ := 4203/250000000) (ψ := -685113/500000) 335 291
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t234 : ((14372802321/250000000000 : ℚ) : ℝ) ≤ stT335 234 := by
  have hc : ((879447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14372802321/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((879447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c235 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-173169/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 300697/625000) (δ := 4203/250000000) (ψ := -685113/500000) 335 291
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t235 : ((-112995777051/5000000000000 : ℚ) : ℝ) ≤ stT335 235 := by
  have hc : ((-173219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112995777051/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-173219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c236 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-122373/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1468107/2000000) (δ := 3361/200000000) (ψ := -685113/500000) 335 292
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t236 : ((-31866491719/500000000000 : ℚ) : ℝ) ≤ stT335 236 := by
  have hc : ((-244771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31866491719/500000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-244771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c237 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((51041/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1899667/5000000) (δ := 3381/200000000) (ψ := -685113/500000) 335 292
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t237 : ((33089694429/10000000000000 : ℚ) : ℝ) ≤ stT335 237 := by
  have hc : ((50941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33089694429/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((50941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c238 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((497021/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3413/125000) (δ := 3361/200000000) (ψ := -685113/500000) 335 292
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t238 : ((322138093113/5000000000000 : ℚ) : ℝ) ≤ stT335 238 := by
  have hc : ((496971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322138093113/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((496971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c239 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((271923/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619257/5000000) (δ := 8399/500000000) (ψ := -685113/500000) 335 292
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t239 : ((87913810129/5000000000000 : ℚ) : ℝ) ≤ stT335 239 := by
  have hc : ((271823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87913810129/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((271823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c240 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-901563/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6735411/10000000) (δ := 3381/200000000) (ψ := -685113/500000) 335 292
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t240 : ((-291010831587/5000000000000 : ℚ) : ℝ) ≤ stT335 240 := by
  have hc : ((-901663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291010831587/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-901663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c241 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-73167/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5490227/10000000) (δ := 8399/500000000) (ψ := -685113/500000) 335 293
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t241 : ((-94278174363/2500000000000 : ℚ) : ℝ) ≤ stT335 241 := by
  have hc : ((-146359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94278174363/2500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-146359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c242 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((345139/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2022307/10000000) (δ := 8399/500000000) (ψ := -685113/500000) 335 293
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t242 : ((27728936417/625000000000 : ℚ) : ℝ) ≤ stT335 242 := by
  have hc : ((345089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27728936417/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((345089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c243 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((42027/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357823/2500000) (δ := 3361/200000000) (ψ := -685113/500000) 335 293
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t243 : ((26957113/500000000 : ℚ) : ℝ) ≤ stT335 243 := by
  have hc : ((21011/25000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26957113/500000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((21011/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c244 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-92149/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4870737/10000000) (δ := 3361/200000000) (ψ := -685113/500000) 335 293
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t244 : ((-5900841219/250000000000 : ℚ) : ℝ) ≤ stT335 244 := by
  have hc : ((-46087/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5900841219/250000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-46087/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c245 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-196881/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7411893/10000000) (δ := 8403/250000000) (ψ := -685113/500000) 335 294
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t245 : ((-125795520177/2000000000000 : ℚ) : ℝ) ≤ stT335 245 := by
  have hc : ((-196901/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125795520177/2000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-196901/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c246 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-5877/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4000463/10000000) (δ := 16891/1000000000) (ψ := -685113/500000) 335 294
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t246 : ((-3759791569/2000000000000 : ℚ) : ℝ) ≤ stT335 246 := by
  have hc : ((-5897/200000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3759791569/2000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-5897/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c247 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((485531/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602893/10000000) (δ := 16891/1000000000) (ψ := -685113/500000) 335 294
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t247 : ((77225948151/1250000000000 : ℚ) : ℝ) ≤ stT335 247 := by
  have hc : ((485481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77225948151/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((485481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c248 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((442531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1390471/5000000) (δ := 16891/1000000000) (ψ := -685113/500000) 335 294
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t248 : ((56188737/2000000000 : ℚ) : ℝ) ≤ stT335 248 := by
  have hc : ((442431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56188737/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((442431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c249 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-388427/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3075563/5000000) (δ := 16791/1000000000) (ψ := -685113/500000) 335 294
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t249 : ((-9847503473/200000000000 : ℚ) : ℝ) ≤ stT335 249 := by
  have hc : ((-388477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9847503473/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-388477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_c250 :
    |Real.cos (((335 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-197257/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6200053/10000000) (δ := 16919/1000000000) (ψ := -685113/500000) 335 295
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st335_t250 : ((-7798261537/156250000000 : ℚ) : ℝ) ≤ stT335 250 := by
  have hc : ((-98641/125000 : ℚ) : ℝ)
      ≤ Real.cos (((335 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st335_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7798261537/156250000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-98641/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st335_p1 : ((24891/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT335 (i+1) := by
  rw [Finset.sum_range_one]
  exact st335_t1

theorem st335_p2 : ((2609490834611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT335 (i+1))
      = (∑ i ∈ Finset.range 1, stT335 (i+1)) + stT335 2 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 1
    simpa using h
  have hprev := st335_p1
  have hstep := st335_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p3 : ((3374162307001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT335 (i+1))
      = (∑ i ∈ Finset.range 2, stT335 (i+1)) + stT335 3 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 2
    simpa using h
  have hprev := st335_p2
  have hstep := st335_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p4 : ((5073752307001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT335 (i+1))
      = (∑ i ∈ Finset.range 3, stT335 (i+1)) + stT335 4 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 3
    simpa using h
  have hprev := st335_p3
  have hstep := st335_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p5 : ((14548528195367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT335 (i+1))
      = (∑ i ∈ Finset.range 4, stT335 (i+1)) + stT335 5 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 4
    simpa using h
  have hprev := st335_p4
  have hstep := st335_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p6 : ((7263137290267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT335 (i+1))
      = (∑ i ∈ Finset.range 5, stT335 (i+1)) + stT335 6 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 5
    simpa using h
  have hprev := st335_p5
  have hstep := st335_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p7 : ((9114667716903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT335 (i+1))
      = (∑ i ∈ Finset.range 6, stT335 (i+1)) + stT335 7 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 6
    simpa using h
  have hprev := st335_p6
  have hstep := st335_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p8 : ((5310973376031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT335 (i+1))
      = (∑ i ∈ Finset.range 7, stT335 (i+1)) + stT335 8 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 7
    simpa using h
  have hprev := st335_p7
  have hstep := st335_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p9 : ((9501698194679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT335 (i+1))
      = (∑ i ∈ Finset.range 8, stT335 (i+1)) + stT335 9 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 8
    simpa using h
  have hprev := st335_p8
  have hstep := st335_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p10 : ((2215092452943/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT335 (i+1))
      = (∑ i ∈ Finset.range 9, stT335 (i+1)) + stT335 10 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 9
    simpa using h
  have hprev := st335_p9
  have hstep := st335_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p11 : ((498137168319/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT335 (i+1))
      = (∑ i ∈ Finset.range 10, stT335 (i+1)) + stT335 11 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 10
    simpa using h
  have hprev := st335_p10
  have hstep := st335_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p12 : ((12055932117831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT335 (i+1))
      = (∑ i ∈ Finset.range 11, stT335 (i+1)) + stT335 12 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 11
    simpa using h
  have hprev := st335_p11
  have hstep := st335_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p13 : ((13422990267831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT335 (i+1))
      = (∑ i ∈ Finset.range 12, stT335 (i+1)) + stT335 13 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 12
    simpa using h
  have hprev := st335_p12
  have hstep := st335_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p14 : ((2922282525607/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT335 (i+1))
      = (∑ i ∈ Finset.range 13, stT335 (i+1)) + stT335 14 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 13
    simpa using h
  have hprev := st335_p13
  have hstep := st335_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p15 : ((27162070121467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT335 (i+1))
      = (∑ i ∈ Finset.range 14, stT335 (i+1)) + stT335 15 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 14
    simpa using h
  have hprev := st335_p14
  have hstep := st335_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p16 : ((29567182621467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT335 (i+1))
      = (∑ i ∈ Finset.range 15, stT335 (i+1)) + stT335 16 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 15
    simpa using h
  have hprev := st335_p15
  have hstep := st335_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p17 : ((29168759525649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT335 (i+1))
      = (∑ i ∈ Finset.range 16, stT335 (i+1)) + stT335 17 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 16
    simpa using h
  have hprev := st335_p16
  have hstep := st335_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p18 : ((5622978423187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT335 (i+1))
      = (∑ i ∈ Finset.range 17, stT335 (i+1)) + stT335 18 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 17
    simpa using h
  have hprev := st335_p17
  have hstep := st335_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p19 : ((28734576039833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT335 (i+1))
      = (∑ i ∈ Finset.range 18, stT335 (i+1)) + stT335 19 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 18
    simpa using h
  have hprev := st335_p18
  have hstep := st335_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p20 : ((7704952285087/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT335 (i+1))
      = (∑ i ∈ Finset.range 19, stT335 (i+1)) + stT335 20 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 19
    simpa using h
  have hprev := st335_p19
  have hstep := st335_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p21 : ((28715099677027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT335 (i+1))
      = (∑ i ∈ Finset.range 20, stT335 (i+1)) + stT335 21 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 20
    simpa using h
  have hprev := st335_p20
  have hstep := st335_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p22 : ((30824865580003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT335 (i+1))
      = (∑ i ∈ Finset.range 21, stT335 (i+1)) + stT335 22 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 21
    simpa using h
  have hprev := st335_p21
  have hstep := st335_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p23 : ((29193827628393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT335 (i+1))
      = (∑ i ∈ Finset.range 22, stT335 (i+1)) + stT335 23 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 22
    simpa using h
  have hprev := st335_p22
  have hstep := st335_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p24 : ((28122449104821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT335 (i+1))
      = (∑ i ∈ Finset.range 23, stT335 (i+1)) + stT335 24 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 23
    simpa using h
  have hprev := st335_p23
  have hstep := st335_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p25 : ((29178785104821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT335 (i+1))
      = (∑ i ∈ Finset.range 24, stT335 (i+1)) + stT335 25 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 24
    simpa using h
  have hprev := st335_p24
  have hstep := st335_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p26 : ((30951553056839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT335 (i+1))
      = (∑ i ∈ Finset.range 25, stT335 (i+1)) + stT335 26 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 25
    simpa using h
  have hprev := st335_p25
  have hstep := st335_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p27 : ((32749051452839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT335 (i+1))
      = (∑ i ∈ Finset.range 26, stT335 (i+1)) + stT335 27 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 26
    simpa using h
  have hprev := st335_p26
  have hstep := st335_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p28 : ((34133896006041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT335 (i+1))
      = (∑ i ∈ Finset.range 27, stT335 (i+1)) + stT335 28 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 27
    simpa using h
  have hprev := st335_p27
  have hstep := st335_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p29 : ((34155577789269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT335 (i+1))
      = (∑ i ∈ Finset.range 28, stT335 (i+1)) + stT335 29 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 28
    simpa using h
  have hprev := st335_p28
  have hstep := st335_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p30 : ((32455329991381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT335 (i+1))
      = (∑ i ∈ Finset.range 29, stT335 (i+1)) + stT335 30 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 29
    simpa using h
  have hprev := st335_p29
  have hstep := st335_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p31 : ((31818670157623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT335 (i+1))
      = (∑ i ∈ Finset.range 30, stT335 (i+1)) + stT335 31 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 30
    simpa using h
  have hprev := st335_p30
  have hstep := st335_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p32 : ((1343450163109/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT335 (i+1))
      = (∑ i ∈ Finset.range 31, stT335 (i+1)) + stT335 32 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 31
    simpa using h
  have hprev := st335_p31
  have hstep := st335_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p33 : ((32485275293197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT335 (i+1))
      = (∑ i ∈ Finset.range 32, stT335 (i+1)) + stT335 33 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 32
    simpa using h
  have hprev := st335_p32
  have hstep := st335_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p34 : ((32671025318547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT335 (i+1))
      = (∑ i ∈ Finset.range 33, stT335 (i+1)) + stT335 34 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 33
    simpa using h
  have hprev := st335_p33
  have hstep := st335_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p35 : ((32969165224203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT335 (i+1))
      = (∑ i ∈ Finset.range 34, stT335 (i+1)) + stT335 35 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 34
    simpa using h
  have hprev := st335_p34
  have hstep := st335_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p36 : ((8163605873647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT335 (i+1))
      = (∑ i ∈ Finset.range 35, stT335 (i+1)) + stT335 36 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 35
    simpa using h
  have hprev := st335_p35
  have hstep := st335_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p37 : ((16280934250789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT335 (i+1))
      = (∑ i ∈ Finset.range 36, stT335 (i+1)) + stT335 37 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 36
    simpa using h
  have hprev := st335_p36
  have hstep := st335_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p38 : ((16702842912337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT335 (i+1))
      = (∑ i ∈ Finset.range 37, stT335 (i+1)) + stT335 38 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 37
    simpa using h
  have hprev := st335_p37
  have hstep := st335_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p39 : ((15938035400933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT335 (i+1))
      = (∑ i ∈ Finset.range 38, stT335 (i+1)) + stT335 39 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 38
    simpa using h
  have hprev := st335_p38
  have hstep := st335_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p40 : ((16570808409671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT335 (i+1))
      = (∑ i ∈ Finset.range 39, stT335 (i+1)) + stT335 40 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 39
    simpa using h
  have hprev := st335_p39
  have hstep := st335_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p41 : ((16744660972511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT335 (i+1))
      = (∑ i ∈ Finset.range 40, stT335 (i+1)) + stT335 41 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 40
    simpa using h
  have hprev := st335_p40
  have hstep := st335_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p42 : ((79865399683/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT335 (i+1))
      = (∑ i ∈ Finset.range 41, stT335 (i+1)) + stT335 42 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 41
    simpa using h
  have hprev := st335_p41
  have hstep := st335_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p43 : ((1599040681617/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT335 (i+1))
      = (∑ i ∈ Finset.range 42, stT335 (i+1)) + stT335 43 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 42
    simpa using h
  have hprev := st335_p42
  have hstep := st335_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p44 : ((8368890359141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT335 (i+1))
      = (∑ i ∈ Finset.range 43, stT335 (i+1)) + stT335 44 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 43
    simpa using h
  have hprev := st335_p43
  have hstep := st335_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p45 : ((17065440486793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT335 (i+1))
      = (∑ i ∈ Finset.range 44, stT335 (i+1)) + stT335 45 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 44
    simpa using h
  have hprev := st335_p44
  have hstep := st335_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p46 : ((16634338509043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT335 (i+1))
      = (∑ i ∈ Finset.range 45, stT335 (i+1)) + stT335 46 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 45
    simpa using h
  have hprev := st335_p45
  have hstep := st335_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p47 : ((15905166667293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT335 (i+1))
      = (∑ i ∈ Finset.range 46, stT335 (i+1)) + stT335 47 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 46
    simpa using h
  have hprev := st335_p46
  have hstep := st335_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p48 : ((15374498655573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT335 (i+1))
      = (∑ i ∈ Finset.range 47, stT335 (i+1)) + stT335 48 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 47
    simpa using h
  have hprev := st335_p47
  have hstep := st335_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p49 : ((15231304312581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT335 (i+1))
      = (∑ i ∈ Finset.range 48, stT335 (i+1)) + stT335 49 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 48
    simpa using h
  have hprev := st335_p48
  have hstep := st335_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p50 : ((15428694506269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT335 (i+1))
      = (∑ i ∈ Finset.range 49, stT335 (i+1)) + stT335 50 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 49
    simpa using h
  have hprev := st335_p49
  have hstep := st335_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p51 : ((15843199090609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT335 (i+1))
      = (∑ i ∈ Finset.range 50, stT335 (i+1)) + stT335 51 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 50
    simpa using h
  have hprev := st335_p50
  have hstep := st335_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p52 : ((8183296951367/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT335 (i+1))
      = (∑ i ∈ Finset.range 51, stT335 (i+1)) + stT335 52 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 51
    simpa using h
  have hprev := st335_p51
  have hstep := st335_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p53 : ((16926592057159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT335 (i+1))
      = (∑ i ∈ Finset.range 52, stT335 (i+1)) + stT335 53 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 52
    simpa using h
  have hprev := st335_p52
  have hstep := st335_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p54 : ((1092053366917/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT335 (i+1))
      = (∑ i ∈ Finset.range 53, stT335 (i+1)) + stT335 54 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 53
    simpa using h
  have hprev := st335_p53
  have hstep := st335_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p55 : ((71818126633/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT335 (i+1))
      = (∑ i ∈ Finset.range 54, stT335 (i+1)) + stT335 55 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 54
    simpa using h
  have hprev := st335_p54
  have hstep := st335_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p56 : ((18303121109563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT335 (i+1))
      = (∑ i ∈ Finset.range 55, stT335 (i+1)) + stT335 56 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 55
    simpa using h
  have hprev := st335_p55
  have hstep := st335_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p57 : ((18431486803811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT335 (i+1))
      = (∑ i ∈ Finset.range 56, stT335 (i+1)) + stT335 57 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 56
    simpa using h
  have hprev := st335_p56
  have hstep := st335_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p58 : ((18261518417951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT335 (i+1))
      = (∑ i ∈ Finset.range 57, stT335 (i+1)) + stT335 58 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 57
    simpa using h
  have hprev := st335_p57
  have hstep := st335_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p59 : ((8893130109363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT335 (i+1))
      = (∑ i ∈ Finset.range 58, stT335 (i+1)) + stT335 59 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 58
    simpa using h
  have hprev := st335_p58
  have hstep := st335_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p60 : ((17143901127571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT335 (i+1))
      = (∑ i ∈ Finset.range 59, stT335 (i+1)) + stT335 60 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 59
    simpa using h
  have hprev := st335_p59
  have hstep := st335_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p61 : ((16632731729487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT335 (i+1))
      = (∑ i ∈ Finset.range 60, stT335 (i+1)) + stT335 61 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 60
    simpa using h
  have hprev := st335_p60
  have hstep := st335_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p62 : ((8288218492917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT335 (i+1))
      = (∑ i ∈ Finset.range 61, stT335 (i+1)) + stT335 62 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 61
    simpa using h
  have hprev := st335_p61
  have hstep := st335_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p63 : ((3408617113861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT335 (i+1))
      = (∑ i ∈ Finset.range 62, stT335 (i+1)) + stT335 63 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 62
    simpa using h
  have hprev := st335_p62
  have hstep := st335_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p64 : ((3529039488861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT335 (i+1))
      = (∑ i ∈ Finset.range 63, stT335 (i+1)) + stT335 64 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 63
    simpa using h
  have hprev := st335_p63
  have hstep := st335_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p65 : ((2221834503411/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT335 (i+1))
      = (∑ i ∈ Finset.range 64, stT335 (i+1)) + stT335 65 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 64
    simpa using h
  have hprev := st335_p64
  have hstep := st335_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p66 : ((17271092698893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT335 (i+1))
      = (∑ i ∈ Finset.range 65, stT335 (i+1)) + stT335 66 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 65
    simpa using h
  have hprev := st335_p65
  have hstep := st335_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p67 : ((16778473510823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT335 (i+1))
      = (∑ i ∈ Finset.range 66, stT335 (i+1)) + stT335 67 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 66
    simpa using h
  have hprev := st335_p66
  have hstep := st335_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p68 : ((1700453669921/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT335 (i+1))
      = (∑ i ∈ Finset.range 67, stT335 (i+1)) + stT335 68 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 67
    simpa using h
  have hprev := st335_p67
  have hstep := st335_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p69 : ((8796964360999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT335 (i+1))
      = (∑ i ∈ Finset.range 68, stT335 (i+1)) + stT335 69 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 68
    simpa using h
  have hprev := st335_p68
  have hstep := st335_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p70 : ((17536506335151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT335 (i+1))
      = (∑ i ∈ Finset.range 69, stT335 (i+1)) + stT335 70 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 69
    simpa using h
  have hprev := st335_p69
  have hstep := st335_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p71 : ((16944008981997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT335 (i+1))
      = (∑ i ∈ Finset.range 70, stT335 (i+1)) + stT335 71 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 70
    simpa using h
  have hprev := st335_p70
  have hstep := st335_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p72 : ((8496594712269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT335 (i+1))
      = (∑ i ∈ Finset.range 71, stT335 (i+1)) + stT335 72 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 71
    simpa using h
  have hprev := st335_p71
  have hstep := st335_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p73 : ((35138736259401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT335 (i+1))
      = (∑ i ∈ Finset.range 72, stT335 (i+1)) + stT335 73 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 72
    simpa using h
  have hprev := st335_p72
  have hstep := st335_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p74 : ((34762140210481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT335 (i+1))
      = (∑ i ∈ Finset.range 73, stT335 (i+1)) + stT335 74 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 73
    simpa using h
  have hprev := st335_p73
  have hstep := st335_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p75 : ((33774882402491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT335 (i+1))
      = (∑ i ∈ Finset.range 74, stT335 (i+1)) + stT335 75 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 74
    simpa using h
  have hprev := st335_p74
  have hstep := st335_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p76 : ((34613999783519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT335 (i+1))
      = (∑ i ∈ Finset.range 75, stT335 (i+1)) + stT335 76 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 75
    simpa using h
  have hprev := st335_p75
  have hstep := st335_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p77 : ((35075298212259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT335 (i+1))
      = (∑ i ∈ Finset.range 76, stT335 (i+1)) + stT335 77 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 76
    simpa using h
  have hprev := st335_p76
  have hstep := st335_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p78 : ((6788664506097/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT335 (i+1))
      = (∑ i ∈ Finset.range 77, stT335 (i+1)) + stT335 78 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 77
    simpa using h
  have hprev := st335_p77
  have hstep := st335_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p79 : ((3439962969051/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT335 (i+1))
      = (∑ i ∈ Finset.range 78, stT335 (i+1)) + stT335 79 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 78
    simpa using h
  have hprev := st335_p78
  have hstep := st335_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p80 : ((35080213272699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT335 (i+1))
      = (∑ i ∈ Finset.range 79, stT335 (i+1)) + stT335 80 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 79
    simpa using h
  have hprev := st335_p79
  have hstep := st335_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p81 : ((33974963499611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT335 (i+1))
      = (∑ i ∈ Finset.range 80, stT335 (i+1)) + stT335 81 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 80
    simpa using h
  have hprev := st335_p80
  have hstep := st335_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p82 : ((34502514652781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT335 (i+1))
      = (∑ i ∈ Finset.range 81, stT335 (i+1)) + stT335 82 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 81
    simpa using h
  have hprev := st335_p81
  have hstep := st335_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p83 : ((34950889335719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT335 (i+1))
      = (∑ i ∈ Finset.range 82, stT335 (i+1)) + stT335 83 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 82
    simpa using h
  have hprev := st335_p82
  have hstep := st335_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p84 : ((33902023427629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT335 (i+1))
      = (∑ i ∈ Finset.range 83, stT335 (i+1)) + stT335 84 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 83
    simpa using h
  have hprev := st335_p83
  have hstep := st335_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p85 : ((34830285963661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT335 (i+1))
      = (∑ i ∈ Finset.range 84, stT335 (i+1)) + stT335 85 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 84
    simpa using h
  have hprev := st335_p84
  have hstep := st335_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p86 : ((34562609369237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT335 (i+1))
      = (∑ i ∈ Finset.range 85, stT335 (i+1)) + stT335 86 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 85
    simpa using h
  have hprev := st335_p85
  have hstep := st335_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p87 : ((532295207267/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT335 (i+1))
      = (∑ i ∈ Finset.range 86, stT335 (i+1)) + stT335 87 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 86
    simpa using h
  have hprev := st335_p86
  have hstep := st335_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p88 : ((35047299422197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT335 (i+1))
      = (∑ i ∈ Finset.range 87, stT335 (i+1)) + stT335 88 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 87
    simpa using h
  have hprev := st335_p87
  have hstep := st335_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p89 : ((1360708340993/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT335 (i+1))
      = (∑ i ∈ Finset.range 88, stT335 (i+1)) + stT335 89 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 88
    simpa using h
  have hprev := st335_p88
  have hstep := st335_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p90 : ((34719610468061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT335 (i+1))
      = (∑ i ∈ Finset.range 89, stT335 (i+1)) + stT335 90 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 89
    simpa using h
  have hprev := st335_p89
  have hstep := st335_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p91 : ((8635873336659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT335 (i+1))
      = (∑ i ∈ Finset.range 90, stT335 (i+1)) + stT335 91 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 90
    simpa using h
  have hprev := st335_p90
  have hstep := st335_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p92 : ((4273122189211/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT335 (i+1))
      = (∑ i ∈ Finset.range 91, stT335 (i+1)) + stT335 92 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 91
    simpa using h
  have hprev := st335_p91
  have hstep := st335_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p93 : ((3495076790109/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT335 (i+1))
      = (∑ i ∈ Finset.range 92, stT335 (i+1)) + stT335 93 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 92
    simpa using h
  have hprev := st335_p92
  have hstep := st335_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p94 : ((16982421994177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT335 (i+1))
      = (∑ i ∈ Finset.range 93, stT335 (i+1)) + stT335 94 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 93
    simpa using h
  have hprev := st335_p93
  have hstep := st335_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p95 : ((4373134435697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT335 (i+1))
      = (∑ i ∈ Finset.range 94, stT335 (i+1)) + stT335 95 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 94
    simpa using h
  have hprev := st335_p94
  have hstep := st335_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p96 : ((34075590926887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT335 (i+1))
      = (∑ i ∈ Finset.range 95, stT335 (i+1)) + stT335 96 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 95
    simpa using h
  have hprev := st335_p95
  have hstep := st335_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p97 : ((34782028059847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT335 (i+1))
      = (∑ i ∈ Finset.range 96, stT335 (i+1)) + stT335 97 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 96
    simpa using h
  have hprev := st335_p96
  have hstep := st335_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p98 : ((3431969214343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT335 (i+1))
      = (∑ i ∈ Finset.range 97, stT335 (i+1)) + stT335 98 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 97
    simpa using h
  have hprev := st335_p97
  have hstep := st335_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p99 : ((34534819308243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT335 (i+1))
      = (∑ i ∈ Finset.range 98, stT335 (i+1)) + stT335 99 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 98
    simpa using h
  have hprev := st335_p98
  have hstep := st335_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p100 : ((17272078149453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT335 (i+1))
      = (∑ i ∈ Finset.range 99, stT335 (i+1)) + stT335 100 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 99
    simpa using h
  have hprev := st335_p99
  have hstep := st335_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p101 : ((8586293891233/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT335 (i+1))
      = (∑ i ∈ Finset.range 100, stT335 (i+1)) + stT335 101 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 100
    simpa using h
  have hprev := st335_p100
  have hstep := st335_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p102 : ((34694025146119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT335 (i+1))
      = (∑ i ∈ Finset.range 101, stT335 (i+1)) + stT335 102 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 101
    simpa using h
  have hprev := st335_p101
  have hstep := st335_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p103 : ((34232939972619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT335 (i+1))
      = (∑ i ∈ Finset.range 102, stT335 (i+1)) + stT335 103 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 102
    simpa using h
  have hprev := st335_p102
  have hstep := st335_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p104 : ((34771862818299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT335 (i+1))
      = (∑ i ∈ Finset.range 103, stT335 (i+1)) + stT335 104 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 103
    simpa using h
  have hprev := st335_p103
  have hstep := st335_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p105 : ((34184126441049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT335 (i+1))
      = (∑ i ∈ Finset.range 104, stT335 (i+1)) + stT335 105 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 104
    simpa using h
  have hprev := st335_p104
  have hstep := st335_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p106 : ((34794738354289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT335 (i+1))
      = (∑ i ∈ Finset.range 105, stT335 (i+1)) + stT335 106 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 105
    simpa using h
  have hprev := st335_p105
  have hstep := st335_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p107 : ((6836759461259/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT335 (i+1))
      = (∑ i ∈ Finset.range 106, stT335 (i+1)) + stT335 107 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 106
    simpa using h
  have hprev := st335_p106
  have hstep := st335_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p108 : ((6954531355709/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT335 (i+1))
      = (∑ i ∈ Finset.range 107, stT335 (i+1)) + stT335 108 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 107
    simpa using h
  have hprev := st335_p107
  have hstep := st335_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p109 : ((1369122986377/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT335 (i+1))
      = (∑ i ∈ Finset.range 108, stT335 (i+1)) + stT335 109 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 108
    simpa using h
  have hprev := st335_p108
  have hstep := st335_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p110 : ((6940748509859/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT335 (i+1))
      = (∑ i ∈ Finset.range 109, stT335 (i+1)) + stT335 110 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 109
    simpa using h
  have hprev := st335_p109
  have hstep := st335_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p111 : ((34323084631711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT335 (i+1))
      = (∑ i ∈ Finset.range 110, stT335 (i+1)) + stT335 111 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 110
    simpa using h
  have hprev := st335_p110
  have hstep := st335_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p112 : ((34579977585281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT335 (i+1))
      = (∑ i ∈ Finset.range 111, stT335 (i+1)) + stT335 112 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 111
    simpa using h
  have hprev := st335_p111
  have hstep := st335_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p113 : ((34475058972151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT335 (i+1))
      = (∑ i ∈ Finset.range 112, stT335 (i+1)) + stT335 113 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 112
    simpa using h
  have hprev := st335_p112
  have hstep := st335_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p114 : ((34401631566337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT335 (i+1))
      = (∑ i ∈ Finset.range 113, stT335 (i+1)) + stT335 114 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 113
    simpa using h
  have hprev := st335_p113
  have hstep := st335_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p115 : ((34671925310769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT335 (i+1))
      = (∑ i ∈ Finset.range 114, stT335 (i+1)) + stT335 115 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 114
    simpa using h
  have hprev := st335_p114
  have hstep := st335_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p116 : ((34198181063243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT335 (i+1))
      = (∑ i ∈ Finset.range 115, stT335 (i+1)) + stT335 116 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 115
    simpa using h
  have hprev := st335_p115
  have hstep := st335_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p117 : ((34862163434743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT335 (i+1))
      = (∑ i ∈ Finset.range 116, stT335 (i+1)) + stT335 117 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 116
    simpa using h
  have hprev := st335_p116
  have hstep := st335_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p118 : ((34045068429343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT335 (i+1))
      = (∑ i ∈ Finset.range 117, stT335 (i+1)) + stT335 118 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 117
    simpa using h
  have hprev := st335_p117
  have hstep := st335_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p119 : ((34949325004087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT335 (i+1))
      = (∑ i ∈ Finset.range 118, stT335 (i+1)) + stT335 119 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 118
    simpa using h
  have hprev := st335_p118
  have hstep := st335_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p120 : ((34050128811667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT335 (i+1))
      = (∑ i ∈ Finset.range 119, stT335 (i+1)) + stT335 120 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 119
    simpa using h
  have hprev := st335_p119
  have hstep := st335_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p121 : ((34831924393507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT335 (i+1))
      = (∑ i ∈ Finset.range 120, stT335 (i+1)) + stT335 121 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 120
    simpa using h
  have hprev := st335_p120
  have hstep := st335_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p122 : ((34283172423979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT335 (i+1))
      = (∑ i ∈ Finset.range 121, stT335 (i+1)) + stT335 122 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 121
    simpa using h
  have hprev := st335_p121
  have hstep := st335_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p123 : ((8625262254033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT335 (i+1))
      = (∑ i ∈ Finset.range 122, stT335 (i+1)) + stT335 123 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 122
    simpa using h
  have hprev := st335_p122
  have hstep := st335_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p124 : ((8666509486239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT335 (i+1))
      = (∑ i ∈ Finset.range 123, stT335 (i+1)) + stT335 124 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 123
    simpa using h
  have hprev := st335_p123
  have hstep := st335_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p125 : ((8533725835857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT335 (i+1))
      = (∑ i ∈ Finset.range 124, stT335 (i+1)) + stT335 125 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 124
    simpa using h
  have hprev := st335_p124
  have hstep := st335_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p126 : ((17465971230339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT335 (i+1))
      = (∑ i ∈ Finset.range 125, stT335 (i+1)) + stT335 126 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 125
    simpa using h
  have hprev := st335_p125
  have hstep := st335_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p127 : ((1702245511667/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT335 (i+1))
      = (∑ i ∈ Finset.range 126, stT335 (i+1)) + stT335 127 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 126
    simpa using h
  have hprev := st335_p126
  have hstep := st335_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p128 : ((34800822000951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT335 (i+1))
      = (∑ i ∈ Finset.range 127, stT335 (i+1)) + stT335 128 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 127
    simpa using h
  have hprev := st335_p127
  have hstep := st335_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p129 : ((34385124104909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT335 (i+1))
      = (∑ i ∈ Finset.range 128, stT335 (i+1)) + stT335 129 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 128
    simpa using h
  have hprev := st335_p128
  have hstep := st335_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p130 : ((4291214487823/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT335 (i+1))
      = (∑ i ∈ Finset.range 129, stT335 (i+1)) + stT335 130 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 129
    simpa using h
  have hprev := st335_p129
  have hstep := st335_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p131 : ((435621795621/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT335 (i+1))
      = (∑ i ∈ Finset.range 130, stT335 (i+1)) + stT335 131 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 130
    simpa using h
  have hprev := st335_p130
  have hstep := st335_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p132 : ((1063401078861/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT335 (i+1))
      = (∑ i ∈ Finset.range 131, stT335 (i+1)) + stT335 132 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 131
    simpa using h
  have hprev := st335_p131
  have hstep := st335_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p133 : ((34863469424393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT335 (i+1))
      = (∑ i ∈ Finset.range 132, stT335 (i+1)) + stT335 133 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 132
    simpa using h
  have hprev := st335_p132
  have hstep := st335_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p134 : ((2145670898133/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT335 (i+1))
      = (∑ i ∈ Finset.range 133, stT335 (i+1)) + stT335 134 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 133
    simpa using h
  have hprev := st335_p133
  have hstep := st335_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p135 : ((17171139214767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT335 (i+1))
      = (∑ i ∈ Finset.range 134, stT335 (i+1)) + stT335 135 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 134
    simpa using h
  have hprev := st335_p134
  have hstep := st335_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p136 : ((17432524642413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT335 (i+1))
      = (∑ i ∈ Finset.range 135, stT335 (i+1)) + stT335 136 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 135
    simpa using h
  have hprev := st335_p135
  have hstep := st335_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p137 : ((17016329268861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT335 (i+1))
      = (∑ i ∈ Finset.range 136, stT335 (i+1)) + stT335 137 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 136
    simpa using h
  have hprev := st335_p136
  have hstep := st335_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p138 : ((17394299701701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT335 (i+1))
      = (∑ i ∈ Finset.range 137, stT335 (i+1)) + stT335 138 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 137
    simpa using h
  have hprev := st335_p137
  have hstep := st335_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p139 : ((34481426908863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT335 (i+1))
      = (∑ i ∈ Finset.range 138, stT335 (i+1)) + stT335 139 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 138
    simpa using h
  have hprev := st335_p138
  have hstep := st335_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p140 : ((17087987607269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT335 (i+1))
      = (∑ i ∈ Finset.range 139, stT335 (i+1)) + stT335 140 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 139
    simpa using h
  have hprev := st335_p139
  have hstep := st335_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p141 : ((34936440093991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT335 (i+1))
      = (∑ i ∈ Finset.range 140, stT335 (i+1)) + stT335 141 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 140
    simpa using h
  have hprev := st335_p140
  have hstep := st335_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p142 : ((34142516018433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT335 (i+1))
      = (∑ i ∈ Finset.range 141, stT335 (i+1)) + stT335 142 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 141
    simpa using h
  have hprev := st335_p141
  have hstep := st335_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p143 : ((34506073900417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT335 (i+1))
      = (∑ i ∈ Finset.range 142, stT335 (i+1)) + stT335 143 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 142
    simpa using h
  have hprev := st335_p142
  have hstep := st335_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p144 : ((34797397117221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT335 (i+1))
      = (∑ i ∈ Finset.range 143, stT335 (i+1)) + stT335 144 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 143
    simpa using h
  have hprev := st335_p143
  have hstep := st335_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p145 : ((34029324235911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT335 (i+1))
      = (∑ i ∈ Finset.range 144, stT335 (i+1)) + stT335 145 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 144
    simpa using h
  have hprev := st335_p144
  have hstep := st335_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p146 : ((34774873855371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT335 (i+1))
      = (∑ i ∈ Finset.range 145, stT335 (i+1)) + stT335 146 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 145
    simpa using h
  have hprev := st335_p145
  have hstep := st335_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p147 : ((34557146583111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT335 (i+1))
      = (∑ i ∈ Finset.range 146, stT335 (i+1)) + stT335 147 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 146
    simpa using h
  have hprev := st335_p146
  have hstep := st335_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p148 : ((8522665077659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT335 (i+1))
      = (∑ i ∈ Finset.range 147, stT335 (i+1)) + stT335 148 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 147
    simpa using h
  have hprev := st335_p147
  have hstep := st335_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p149 : ((17453535758767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT335 (i+1))
      = (∑ i ∈ Finset.range 148, stT335 (i+1)) + stT335 149 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 148
    simpa using h
  have hprev := st335_p148
  have hstep := st335_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p150 : ((8587345709403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT335 (i+1))
      = (∑ i ∈ Finset.range 149, stT335 (i+1)) + stT335 150 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 149
    simpa using h
  have hprev := st335_p149
  have hstep := st335_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p151 : ((34216526086839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT335 (i+1))
      = (∑ i ∈ Finset.range 150, stT335 (i+1)) + stT335 151 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 150
    simpa using h
  have hprev := st335_p150
  have hstep := st335_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p152 : ((34937181678627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT335 (i+1))
      = (∑ i ∈ Finset.range 151, stT335 (i+1)) + stT335 152 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 151
    simpa using h
  have hprev := st335_p151
  have hstep := st335_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p153 : ((34215693967837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT335 (i+1))
      = (∑ i ∈ Finset.range 152, stT335 (i+1)) + stT335 153 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 152
    simpa using h
  have hprev := st335_p152
  have hstep := st335_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p154 : ((34330702495321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT335 (i+1))
      = (∑ i ∈ Finset.range 153, stT335 (i+1)) + stT335 154 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 153
    simpa using h
  have hprev := st335_p153
  have hstep := st335_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p155 : ((6984667671443/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT335 (i+1))
      = (∑ i ∈ Finset.range 154, stT335 (i+1)) + stT335 155 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 154
    simpa using h
  have hprev := st335_p154
  have hstep := st335_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p156 : ((34146806259007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT335 (i+1))
      = (∑ i ∈ Finset.range 155, stT335 (i+1)) + stT335 156 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 155
    simpa using h
  have hprev := st335_p155
  have hstep := st335_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p157 : ((34400313488391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT335 (i+1))
      = (∑ i ∈ Finset.range 156, stT335 (i+1)) + stT335 157 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 156
    simpa using h
  have hprev := st335_p156
  have hstep := st335_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p158 : ((34907409475761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT335 (i+1))
      = (∑ i ∈ Finset.range 157, stT335 (i+1)) + stT335 158 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 157
    simpa using h
  have hprev := st335_p157
  have hstep := st335_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p159 : ((6824600665733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT335 (i+1))
      = (∑ i ∈ Finset.range 158, stT335 (i+1)) + stT335 159 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 158
    simpa using h
  have hprev := st335_p158
  have hstep := st335_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p160 : ((1376677159087/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT335 (i+1))
      = (∑ i ∈ Finset.range 159, stT335 (i+1)) + stT335 160 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 159
    simpa using h
  have hprev := st335_p159
  have hstep := st335_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p161 : ((6981662166703/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT335 (i+1))
      = (∑ i ∈ Finset.range 160, stT335 (i+1)) + stT335 161 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 160
    simpa using h
  have hprev := st335_p160
  have hstep := st335_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p162 : ((1706692881477/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT335 (i+1))
      = (∑ i ∈ Finset.range 161, stT335 (i+1)) + stT335 162 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 161
    simpa using h
  have hprev := st335_p161
  have hstep := st335_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p163 : ((1719043716787/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT335 (i+1))
      = (∑ i ∈ Finset.range 162, stT335 (i+1)) + stT335 163 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 162
    simpa using h
  have hprev := st335_p162
  have hstep := st335_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p164 : ((8731336370223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT335 (i+1))
      = (∑ i ∈ Finset.range 163, stT335 (i+1)) + stT335 164 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 163
    simpa using h
  have hprev := st335_p163
  have hstep := st335_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p165 : ((1367317725761/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT335 (i+1))
      = (∑ i ∈ Finset.range 164, stT335 (i+1)) + stT335 165 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 164
    simpa using h
  have hprev := st335_p164
  have hstep := st335_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p166 : ((1371872080823/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT335 (i+1))
      = (∑ i ∈ Finset.range 165, stT335 (i+1)) + stT335 166 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 165
    simpa using h
  have hprev := st335_p165
  have hstep := st335_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p167 : ((34940337989711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT335 (i+1))
      = (∑ i ∈ Finset.range 166, stT335 (i+1)) + stT335 167 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 166
    simpa using h
  have hprev := st335_p166
  have hstep := st335_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p168 : ((34283749248099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT335 (i+1))
      = (∑ i ∈ Finset.range 167, stT335 (i+1)) + stT335 168 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 167
    simpa using h
  have hprev := st335_p167
  have hstep := st335_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p169 : ((17089814993047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT335 (i+1))
      = (∑ i ∈ Finset.range 168, stT335 (i+1)) + stT335 169 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 168
    simpa using h
  have hprev := st335_p168
  have hstep := st335_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p170 : ((3491874475629/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT335 (i+1))
      = (∑ i ∈ Finset.range 169, stT335 (i+1)) + stT335 170 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 169
    simpa using h
  have hprev := st335_p169
  have hstep := st335_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p171 : ((3444742640813/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT335 (i+1))
      = (∑ i ∈ Finset.range 170, stT335 (i+1)) + stT335 171 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 170
    simpa using h
  have hprev := st335_p170
  have hstep := st335_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p172 : ((17032821556529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT335 (i+1))
      = (∑ i ∈ Finset.range 171, stT335 (i+1)) + stT335 172 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 171
    simpa using h
  have hprev := st335_p171
  have hstep := st335_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p173 : ((17408481416169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT335 (i+1))
      = (∑ i ∈ Finset.range 172, stT335 (i+1)) + stT335 173 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 172
    simpa using h
  have hprev := st335_p172
  have hstep := st335_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p174 : ((17330547322771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT335 (i+1))
      = (∑ i ∈ Finset.range 173, stT335 (i+1)) + stT335 174 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 173
    simpa using h
  have hprev := st335_p173
  have hstep := st335_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p175 : ((8504735129833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT335 (i+1))
      = (∑ i ∈ Finset.range 174, stT335 (i+1)) + stT335 175 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 174
    simpa using h
  have hprev := st335_p174
  have hstep := st335_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p176 : ((8651624602471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT335 (i+1))
      = (∑ i ∈ Finset.range 175, stT335 (i+1)) + stT335 176 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 175
    simpa using h
  have hprev := st335_p175
  have hstep := st335_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p177 : ((2178990153593/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT335 (i+1))
      = (∑ i ∈ Finset.range 176, stT335 (i+1)) + stT335 177 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 176
    simpa using h
  have hprev := st335_p176
  have hstep := st335_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p178 : ((8528660999807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT335 (i+1))
      = (∑ i ∈ Finset.range 177, stT335 (i+1)) + stT335 178 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 177
    simpa using h
  have hprev := st335_p177
  have hstep := st335_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p179 : ((34316059045853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT335 (i+1))
      = (∑ i ∈ Finset.range 178, stT335 (i+1)) + stT335 179 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 178
    simpa using h
  have hprev := st335_p178
  have hstep := st335_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p180 : ((4368015716051/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT335 (i+1))
      = (∑ i ∈ Finset.range 179, stT335 (i+1)) + stT335 180 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 179
    simpa using h
  have hprev := st335_p179
  have hstep := st335_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p181 : ((34383860432503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT335 (i+1))
      = (∑ i ∈ Finset.range 180, stT335 (i+1)) + stT335 181 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 180
    simpa using h
  have hprev := st335_p180
  have hstep := st335_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p182 : ((34066540202503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT335 (i+1))
      = (∑ i ∈ Finset.range 181, stT335 (i+1)) + stT335 182 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 181
    simpa using h
  have hprev := st335_p181
  have hstep := st335_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p183 : ((8698520562481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT335 (i+1))
      = (∑ i ∈ Finset.range 182, stT335 (i+1)) + stT335 183 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 182
    simpa using h
  have hprev := st335_p182
  have hstep := st335_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p184 : ((17368506306097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT335 (i+1))
      = (∑ i ∈ Finset.range 183, stT335 (i+1)) + stT335 184 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 183
    simpa using h
  have hprev := st335_p183
  have hstep := st335_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p185 : ((34039586927979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT335 (i+1))
      = (∑ i ∈ Finset.range 184, stT335 (i+1)) + stT335 185 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 184
    simpa using h
  have hprev := st335_p184
  have hstep := st335_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p186 : ((34427412517119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT335 (i+1))
      = (∑ i ∈ Finset.range 185, stT335 (i+1)) + stT335 186 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 185
    simpa using h
  have hprev := st335_p185
  have hstep := st335_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p187 : ((34945705203479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT335 (i+1))
      = (∑ i ∈ Finset.range 186, stT335 (i+1)) + stT335 187 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 186
    simpa using h
  have hprev := st335_p186
  have hstep := st335_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p188 : ((34332407059079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT335 (i+1))
      = (∑ i ∈ Finset.range 187, stT335 (i+1)) + stT335 188 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 187
    simpa using h
  have hprev := st335_p187
  have hstep := st335_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p189 : ((34072282593563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT335 (i+1))
      = (∑ i ∈ Finset.range 188, stT335 (i+1)) + stT335 189 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 188
    simpa using h
  have hprev := st335_p188
  have hstep := st335_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p190 : ((34787398796283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT335 (i+1))
      = (∑ i ∈ Finset.range 189, stT335 (i+1)) + stT335 190 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 189
    simpa using h
  have hprev := st335_p189
  have hstep := st335_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p191 : ((34773471424683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT335 (i+1))
      = (∑ i ∈ Finset.range 190, stT335 (i+1)) + stT335 191 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 190
    simpa using h
  have hprev := st335_p190
  have hstep := st335_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p192 : ((34065767573059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT335 (i+1))
      = (∑ i ∈ Finset.range 191, stT335 (i+1)) + stT335 192 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 191
    simpa using h
  have hprev := st335_p191
  have hstep := st335_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p193 : ((34324078944329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT335 (i+1))
      = (∑ i ∈ Finset.range 192, stT335 (i+1)) + stT335 193 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 192
    simpa using h
  have hprev := st335_p192
  have hstep := st335_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p194 : ((34944322860529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT335 (i+1))
      = (∑ i ∈ Finset.range 193, stT335 (i+1)) + stT335 194 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 193
    simpa using h
  have hprev := st335_p193
  have hstep := st335_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p195 : ((17247202138337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT335 (i+1))
      = (∑ i ∈ Finset.range 194, stT335 (i+1)) + stT335 195 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 194
    simpa using h
  have hprev := st335_p194
  have hstep := st335_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p196 : ((17004030612497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT335 (i+1))
      = (∑ i ∈ Finset.range 195, stT335 (i+1)) + stT335 196 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 195
    simpa using h
  have hprev := st335_p195
  have hstep := st335_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p197 : ((17295004785437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT335 (i+1))
      = (∑ i ∈ Finset.range 196, stT335 (i+1)) + stT335 197 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 196
    simpa using h
  have hprev := st335_p196
  have hstep := st335_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p198 : ((2182749989883/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT335 (i+1))
      = (∑ i ∈ Finset.range 197, stT335 (i+1)) + stT335 198 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 197
    simpa using h
  have hprev := st335_p197
  have hstep := st335_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p199 : ((17131830684303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT335 (i+1))
      = (∑ i ∈ Finset.range 198, stT335 (i+1)) + stT335 199 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 198
    simpa using h
  have hprev := st335_p198
  have hstep := st335_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p200 : ((3407900178977/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT335 (i+1))
      = (∑ i ∈ Finset.range 199, stT335 (i+1)) + stT335 200 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 199
    simpa using h
  have hprev := st335_p199
  have hstep := st335_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p201 : ((6954961117591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT335 (i+1))
      = (∑ i ∈ Finset.range 200, stT335 (i+1)) + stT335 201 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 200
    simpa using h
  have hprev := st335_p200
  have hstep := st335_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p202 : ((34825595440997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT335 (i+1))
      = (∑ i ∈ Finset.range 201, stT335 (i+1)) + stT335 202 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 201
    simpa using h
  have hprev := st335_p201
  have hstep := st335_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p203 : ((17061853236033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT335 (i+1))
      = (∑ i ∈ Finset.range 202, stT335 (i+1)) + stT335 203 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 202
    simpa using h
  have hprev := st335_p202
  have hstep := st335_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p204 : ((17092088781933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT335 (i+1))
      = (∑ i ∈ Finset.range 203, stT335 (i+1)) + stT335 204 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 203
    simpa using h
  have hprev := st335_p203
  have hstep := st335_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p205 : ((17437139742273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT335 (i+1))
      = (∑ i ∈ Finset.range 204, stT335 (i+1)) + stT335 205 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 204
    simpa using h
  have hprev := st335_p204
  have hstep := st335_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p206 : ((434083899001/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT335 (i+1))
      = (∑ i ∈ Finset.range 205, stT335 (i+1)) + stT335 206 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 205
    simpa using h
  have hprev := st335_p205
  have hstep := st335_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p207 : ((2128488578933/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT335 (i+1))
      = (∑ i ∈ Finset.range 206, stT335 (i+1)) + stT335 207 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 206
    simpa using h
  have hprev := st335_p206
  have hstep := st335_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p208 : ((34266248948303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT335 (i+1))
      = (∑ i ∈ Finset.range 207, stT335 (i+1)) + stT335 208 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 207
    simpa using h
  have hprev := st335_p207
  have hstep := st335_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p209 : ((6983455681193/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT335 (i+1))
      = (∑ i ∈ Finset.range 208, stT335 (i+1)) + stT335 209 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 208
    simpa using h
  have hprev := st335_p208
  have hstep := st335_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p210 : ((34665968789953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT335 (i+1))
      = (∑ i ∈ Finset.range 209, stT335 (i+1)) + stT335 210 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 209
    simpa using h
  have hprev := st335_p209
  have hstep := st335_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p211 : ((132929817147/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT335 (i+1))
      = (∑ i ∈ Finset.range 210, stT335 (i+1)) + stT335 211 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 210
    simpa using h
  have hprev := st335_p210
  have hstep := st335_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p212 : ((8575368112419/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT335 (i+1))
      = (∑ i ∈ Finset.range 211, stT335 (i+1)) + stT335 212 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 211
    simpa using h
  have hprev := st335_p211
  have hstep := st335_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p213 : ((8732307340473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT335 (i+1))
      = (∑ i ∈ Finset.range 212, stT335 (i+1)) + stT335 213 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 212
    simpa using h
  have hprev := st335_p212
  have hstep := st335_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p214 : ((8664105281667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT335 (i+1))
      = (∑ i ∈ Finset.range 213, stT335 (i+1)) + stT335 214 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 213
    simpa using h
  have hprev := st335_p213
  have hstep := st335_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p215 : ((17014280762889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT335 (i+1))
      = (∑ i ∈ Finset.range 214, stT335 (i+1)) + stT335 215 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 214
    simpa using h
  have hprev := st335_p214
  have hstep := st335_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p216 : ((8571026059047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT335 (i+1))
      = (∑ i ∈ Finset.range 215, stT335 (i+1)) + stT335 216 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 215
    simpa using h
  have hprev := st335_p215
  have hstep := st335_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p217 : ((8729741822779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT335 (i+1))
      = (∑ i ∈ Finset.range 216, stT335 (i+1)) + stT335 217 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 216
    simpa using h
  have hprev := st335_p216
  have hstep := st335_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p218 : ((8674683211981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT335 (i+1))
      = (∑ i ∈ Finset.range 217, stT335 (i+1)) + stT335 218 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 217
    simpa using h
  have hprev := st335_p217
  have hstep := st335_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p219 : ((17025910577633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT335 (i+1))
      = (∑ i ∈ Finset.range 218, stT335 (i+1)) + stT335 219 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 218
    simpa using h
  have hprev := st335_p218
  have hstep := st335_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p220 : ((8554455945361/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT335 (i+1))
      = (∑ i ∈ Finset.range 219, stT335 (i+1)) + stT335 220 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 219
    simpa using h
  have hprev := st335_p219
  have hstep := st335_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p221 : ((8719341978673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT335 (i+1))
      = (∑ i ∈ Finset.range 220, stT335 (i+1)) + stT335 221 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 220
    simpa using h
  have hprev := st335_p220
  have hstep := st335_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p222 : ((3478432810441/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT335 (i+1))
      = (∑ i ∈ Finset.range 221, stT335 (i+1)) + stT335 222 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 221
    simpa using h
  have hprev := st335_p221
  have hstep := st335_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p223 : ((3411643392671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT335 (i+1))
      = (∑ i ∈ Finset.range 222, stT335 (i+1)) + stT335 223 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 222
    simpa using h
  have hprev := st335_p222
  have hstep := st335_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p224 : ((6823526652269/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT335 (i+1))
      = (∑ i ∈ Finset.range 223, stT335 (i+1)) + stT335 224 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 223
    simpa using h
  have hprev := st335_p223
  have hstep := st335_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p225 : ((34782273930037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT335 (i+1))
      = (∑ i ∈ Finset.range 224, stT335 (i+1)) + stT335 225 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 224
    simpa using h
  have hprev := st335_p224
  have hstep := st335_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p226 : ((34889431382707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT335 (i+1))
      = (∑ i ∈ Finset.range 225, stT335 (i+1)) + stT335 226 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 225
    simpa using h
  have hprev := st335_p225
  have hstep := st335_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p227 : ((34246878850859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT335 (i+1))
      = (∑ i ∈ Finset.range 226, stT335 (i+1)) + stT335 227 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 226
    simpa using h
  have hprev := st335_p226
  have hstep := st335_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p228 : ((8504631469481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT335 (i+1))
      = (∑ i ∈ Finset.range 227, stT335 (i+1)) + stT335 228 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 227
    simpa using h
  have hprev := st335_p227
  have hstep := st335_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p229 : ((17305786843967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT335 (i+1))
      = (∑ i ∈ Finset.range 228, stT335 (i+1)) + stT335 229 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 228
    simpa using h
  have hprev := st335_p228
  have hstep := st335_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p230 : ((17483033792697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT335 (i+1))
      = (∑ i ∈ Finset.range 229, stT335 (i+1)) + stT335 230 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 229
    simpa using h
  have hprev := st335_p229
  have hstep := st335_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p231 : ((17228268856729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT335 (i+1))
      = (∑ i ∈ Finset.range 230, stT335 (i+1)) + stT335 231 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 230
    simpa using h
  have hprev := st335_p230
  have hstep := st335_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p232 : ((6796291329493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT335 (i+1))
      = (∑ i ∈ Finset.range 231, stT335 (i+1)) + stT335 232 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 231
    simpa using h
  have hprev := st335_p231
  have hstep := st335_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p233 : ((34368398625147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT335 (i+1))
      = (∑ i ∈ Finset.range 232, stT335 (i+1)) + stT335 233 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 232
    simpa using h
  have hprev := st335_p232
  have hstep := st335_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p234 : ((34943310717987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT335 (i+1))
      = (∑ i ∈ Finset.range 233, stT335 (i+1)) + stT335 234 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 233
    simpa using h
  have hprev := st335_p233
  have hstep := st335_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p235 : ((6943463832777/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT335 (i+1))
      = (∑ i ∈ Finset.range 234, stT335 (i+1)) + stT335 235 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 234
    simpa using h
  have hprev := st335_p234
  have hstep := st335_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p236 : ((6815997865901/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT335 (i+1))
      = (∑ i ∈ Finset.range 235, stT335 (i+1)) + stT335 236 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 235
    simpa using h
  have hprev := st335_p235
  have hstep := st335_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p237 : ((17056539511967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT335 (i+1))
      = (∑ i ∈ Finset.range 236, stT335 (i+1)) + stT335 237 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 236
    simpa using h
  have hprev := st335_p236
  have hstep := st335_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p238 : ((434466940127/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT335 (i+1))
      = (∑ i ∈ Finset.range 237, stT335 (i+1)) + stT335 238 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 237
    simpa using h
  have hprev := st335_p237
  have hstep := st335_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p239 : ((17466591415209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT335 (i+1))
      = (∑ i ∈ Finset.range 238, stT335 (i+1)) + stT335 239 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 238
    simpa using h
  have hprev := st335_p238
  have hstep := st335_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p240 : ((8587790291811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT335 (i+1))
      = (∑ i ∈ Finset.range 239, stT335 (i+1)) + stT335 240 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 239
    simpa using h
  have hprev := st335_p239
  have hstep := st335_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p241 : ((1061689014681/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT335 (i+1))
      = (∑ i ∈ Finset.range 240, stT335 (i+1)) + stT335 241 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 240
    simpa using h
  have hprev := st335_p240
  have hstep := st335_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p242 : ((2151106965779/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT335 (i+1))
      = (∑ i ∈ Finset.range 241, stT335 (i+1)) + stT335 242 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 241
    simpa using h
  have hprev := st335_p241
  have hstep := st335_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p243 : ((2184803357029/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT335 (i+1))
      = (∑ i ∈ Finset.range 242, stT335 (i+1)) + stT335 243 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 242
    simpa using h
  have hprev := st335_p242
  have hstep := st335_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p244 : ((4340102507963/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT335 (i+1))
      = (∑ i ∈ Finset.range 243, stT335 (i+1)) + stT335 244 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 243
    simpa using h
  have hprev := st335_p243
  have hstep := st335_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p245 : ((34091842462819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT335 (i+1))
      = (∑ i ∈ Finset.range 244, stT335 (i+1)) + stT335 245 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 244
    simpa using h
  have hprev := st335_p244
  have hstep := st335_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p246 : ((17036521752487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT335 (i+1))
      = (∑ i ∈ Finset.range 245, stT335 (i+1)) + stT335 246 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 245
    simpa using h
  have hprev := st335_p245
  have hstep := st335_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p247 : ((17345425545091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT335 (i+1))
      = (∑ i ∈ Finset.range 246, stT335 (i+1)) + stT335 247 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 246
    simpa using h
  have hprev := st335_p246
  have hstep := st335_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p248 : ((17485897387591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT335 (i+1))
      = (∑ i ∈ Finset.range 247, stT335 (i+1)) + stT335 248 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 247
    simpa using h
  have hprev := st335_p247
  have hstep := st335_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p249 : ((8619854900383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT335 (i+1))
      = (∑ i ∈ Finset.range 248, stT335 (i+1)) + stT335 249 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 248
    simpa using h
  have hprev := st335_p248
  have hstep := st335_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_p250 : ((8495082715791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT335 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT335 (i+1))
      = (∑ i ∈ Finset.range 249, stT335 (i+1)) + stT335 250 := by
    have h := Finset.sum_range_succ (fun i => stT335 (i+1)) 249
    simpa using h
  have hprev := st335_p249
  have hstep := st335_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st335_s250 :
    |Real.sin (((335 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))
      - ((-307179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -6200053/10000000) (δ := 16919/1000000000) (ψ := -685113/500000) 335 295
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 335`** (evaluated boundary). -/
theorem station_335_sign : hardyG ((((335:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 335 250 (by norm_num) (by norm_num)
    ((-685113/500000 : ℚ) : ℝ)
  have hchain := st335_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT335 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((335 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-685113/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st335_c250
  have hsinb := abs_le.mp st335_s250
  have hbdy_lo : ((13039381276477/448901000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((335 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-685113/500000 : ℚ) : ℝ))) / 2
          - ((((335:ℕ)):ℝ))
            * Real.sin (((335 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-685113/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((335:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((335:ℝ) * Real.log (250:ℝ) - ((-685113/500000 : ℚ) : ℝ))) / 2
        - ((335:ℝ)) * Real.sin ((335:ℝ) * Real.log (250:ℝ) - ((-685113/500000 : ℚ) : ℝ))
        ≥ ((103085447/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((335:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((103085447/500000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((103085447/500000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((103085447/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((335:ℕ)):ℝ))+1) * (((((335:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((47521241757/19531250000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8495082715791/2500000000000 : ℚ) : ℝ) + ((13039381276477/448901000000000 : ℚ) : ℝ)
      - ((47521241757/19531250000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-685113/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((335:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-685113/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((335:ℕ)):ℝ)))).re
      - Real.sin ((-685113/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((335:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((335:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((335:ℕ)):ℝ))
      = (((((335:ℕ)):ℝ)) * (Real.log ((((335:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((335:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_335
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
  have hθwin : |(((-685113/500000 : ℚ) : ℝ) + ((80:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((335:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((335:ℕ)):ℝ)))
    (φ := ((-685113/500000 : ℚ) : ℝ) + ((80:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-685113/500000 : ℚ) : ℝ) + ((80:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-685113/500000 : ℚ)) : ℝ) - Real.pi) + ((80:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-685113/500000 : ℚ)) : ℝ) - Real.pi) 80).1,
    (cos_sin_shift ((((-685113/500000 : ℚ)) : ℝ) - Real.pi) 80).2]
  exact cos_sin_flip ((-685113/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_335_sign
end AxiomAudit
