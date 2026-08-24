import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 277` (rung-280.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT277 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((277 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-182979/200000 : ℚ) : ℝ))

theorem st277_c1 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((304937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1143619/5000000) (δ := 201/1000000000) (ψ := -182979/200000) 277 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t1 : ((19057/31250 : ℚ) : ℝ) ≤ stT277 1 := by
  have hc : ((19057/31250 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19057/31250 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((19057/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c2 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-28719/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2327611/5000000) (δ := 1753/125000000) (ψ := -182979/200000) 277 31
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t2 : ((-12694334827/62500000000 : ℚ) : ℝ) ≤ stT277 2 := by
  have hc : ((-7181/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12694334827/62500000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-7181/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c3 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-879493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330699/500000) (δ := 281/20000000) (ψ := -182979/200000) 277 49
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t3 : ((-5078044149129/10000000000000 : ℚ) : ℝ) ≤ stT277 3 := by
  have hc : ((-879543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5078044149129/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-879543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c4 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-4579/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1027579/2500000) (δ := 14039/1000000000) (ψ := -182979/200000) 277 61
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t4 : ((-183285036657/5000000000000 : ℚ) : ℝ) ≤ stT277 4 := by
  have hc : ((-36657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183285036657/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-36657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c5 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((406051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778813/5000000) (δ := 13911/1000000000) (ψ := -182979/200000) 277 71
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t5 : ((181580308551/500000000000 : ℚ) : ℝ) ≤ stT277 5 := by
  have hc : ((203013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181580308551/500000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((203013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c6 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((130393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1075779/5000000) (δ := 7017/500000000) (ψ := -182979/200000) 277 79
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t6 : ((266143125303/1000000000000 : ℚ) : ℝ) ≤ stT277 6 := by
  have hc : ((130383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266143125303/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((130383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c7 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((9123/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42193/400000) (δ := 437/31250000) (ψ := -182979/200000) 277 86
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t7 : ((3447980239/10000000000 : ℚ) : ℝ) ≤ stT277 7 := by
  have hc : ((3649/4000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3447980239/10000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((3649/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c8 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((212043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283211/1000000) (δ := 13941/1000000000) (ψ := -182979/200000) 277 92
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t8 : ((374798317797/2500000000000 : ℚ) : ℝ) ≤ stT277 8 := by
  have hc : ((106009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374798317797/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((106009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c9 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((249257/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192801/10000000) (δ := 2801/200000000) (ψ := -182979/200000) 277 97
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t9 : ((1661629833837/5000000000000 : ℚ) : ℝ) ≤ stT277 9 := by
  have hc : ((498489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1661629833837/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((498489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c10 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-550657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5384869/10000000) (δ := 13969/1000000000) (ψ := -182979/200000) 277 102
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t10 : ((-870744315273/5000000000000 : ℚ) : ℝ) ≤ stT277 10 := by
  have hc : ((-550707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-870744315273/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-550707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c11 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((632699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -276801/1250000) (δ := 13963/1000000000) (ψ := -182979/200000) 277 106
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t11 : ((1907508224337/10000000000000 : ℚ) : ℝ) ≤ stT277 11 := by
  have hc : ((632649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1907508224337/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((632649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c12 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-67743/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4790867/10000000) (δ := 1739/125000000) (ψ := -182979/200000) 277 110
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t12 : ((-6112065883/62500000000 : ℚ) : ℝ) ≤ stT277 12 := by
  have hc : ((-67753/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6112065883/62500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-67753/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c13 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((1313/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3514813/10000000) (δ := 1389/100000000) (ψ := -182979/200000) 277 113
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t13 : ((36404961/800000000 : ℚ) : ℝ) ≤ stT277 13 := by
  have hc : ((6563/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36404961/800000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((6563/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c14 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-499179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7710713/10000000) (δ := 13969/1000000000) (ψ := -182979/200000) 277 116
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t14 : ((-333544775013/1250000000000 : ℚ) : ℝ) ≤ stT277 14 := by
  have hc : ((-124801/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333544775013/1250000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-124801/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c15 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-97923/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7343557/10000000) (δ := 351/25000000) (ψ := -182979/200000) 277 120
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t15 : ((-31606127349/125000000000 : ℚ) : ℝ) ≤ stT277 15 := by
  have hc : ((-12241/12500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31606127349/125000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-12241/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c16 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-179787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1483357/2500000) (δ := 6963/500000000) (ψ := -182979/200000) 277 122
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t16 : ((-898997859599/5000000000000 : ℚ) : ℝ) ≤ stT277 16 := by
  have hc : ((-359599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-898997859599/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-359599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c17 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((237557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 396037/5000000) (δ := 13899/1000000000) (ψ := -182979/200000) 277 125
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t17 : ((288064989171/1250000000000 : ℚ) : ℝ) ≤ stT277 17 := by
  have hc : ((475089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((288064989171/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((475089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c18 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-113001/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -843703/1250000) (δ := 13883/1000000000) (ψ := -182979/200000) 277 128
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t18 : ((-1065442749667/5000000000000 : ℚ) : ℝ) ≤ stT277 18 := by
  have hc : ((-452029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1065442749667/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-452029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c19 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((958357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362007/5000000) (δ := 2807/200000000) (ψ := -182979/200000) 277 130
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t19 : ((2198506712199/10000000000000 : ℚ) : ℝ) ≤ stT277 19 := by
  have hc : ((958307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2198506712199/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((958307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c20 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((108397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3380669/10000000) (δ := 6977/500000000) (ψ := -182979/200000) 277 132
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t20 : ((60581763231/1250000000000 : ℚ) : ℝ) ≤ stT277 20 := by
  have hc : ((27093/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60581763231/1250000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((27093/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c21 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-666859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1437989/2500000) (δ := 13939/1000000000) (ψ := -182979/200000) 277 134
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t21 : ((-1455314814711/10000000000000 : ℚ) : ℝ) ≤ stT277 21 := by
  have hc : ((-666909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1455314814711/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-666909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c22 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-216813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655113/1000000) (δ := 6989/500000000) (ψ := -182979/200000) 277 136
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t22 : ((-115568425151/625000000000 : ℚ) : ℝ) ≤ stT277 22 := by
  have hc : ((-433651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115568425151/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-433651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c23 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-714867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236723/400000) (δ := 1749/125000000) (ψ := -182979/200000) 277 138
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t23 : ((-298141121593/2000000000000 : ℚ) : ℝ) ≤ stT277 23 := by
  have hc : ((-714917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298141121593/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-714917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c24 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-19071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3974671/10000000) (δ := 1737/125000000) (ψ := -182979/200000) 277 140
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t24 : ((-19515294141/5000000000000 : ℚ) : ℝ) ≤ stT277 24 := by
  have hc : ((-19121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19515294141/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-19121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c25 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((189131/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41399/500000) (δ := 14021/1000000000) (ψ := -182979/200000) 277 142
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t25 : ((189121/1000000 : ℚ) : ℝ) ≤ stT277 25 := by
  have hc : ((189121/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189121/1000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((189121/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c26 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((99213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -856903/2500000) (δ := 2787/200000000) (ψ := -182979/200000) 277 144
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t26 : ((48630909317/1250000000000 : ℚ) : ℝ) ≤ stT277 26 := by
  have hc : ((24797/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48630909317/1250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((24797/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c27 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-471083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3499791/5000000) (δ := 349/25000000) (ψ := -182979/200000) 277 145
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t27 : ((-226661954277/1250000000000 : ℚ) : ℝ) ≤ stT277 27 := by
  have hc : ((-117777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226661954277/1250000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-117777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c28 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((953149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24009/312500) (δ := 13857/1000000000) (ψ := -182979/200000) 277 147
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t28 : ((900593729189/5000000000000 : ℚ) : ℝ) ≤ stT277 28 := by
  have hc : ((953099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((900593729189/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((953099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c29 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-102967/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6346913/10000000) (δ := 13971/1000000000) (ψ := -182979/200000) 277 149
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t29 : ((-382433176961/2500000000000 : ℚ) : ℝ) ≤ stT277 29 := by
  have hc : ((-411893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382433176961/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-411893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c30 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((842567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177739/1250000) (δ := 557/40000000) (ψ := -182979/200000) 277 150
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t30 : ((1538217830097/10000000000000 : ℚ) : ℝ) ≤ stT277 30 := by
  have hc : ((842517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1538217830097/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((842517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c31 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-974393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7287009/10000000) (δ := 1401/100000000) (ψ := -182979/200000) 277 152
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t31 : ((-875076123961/5000000000000 : ℚ) : ℝ) ≤ stT277 31 := by
  have hc : ((-974443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-875076123961/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-974443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c32 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((459827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1008997/10000000) (δ := 139/10000000) (ψ := -182979/200000) 277 153
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t32 : ((203205585583/1250000000000 : ℚ) : ℝ) ≤ stT277 32 := by
  have hc : ((229901/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203205585583/1250000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((229901/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c33 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-131511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4592373/10000000) (δ := 14007/1000000000) (ψ := -182979/200000) 277 154
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t33 : ((-14310927717/312500000000 : ℚ) : ℝ) ≤ stT277 33 := by
  have hc : ((-8221/31250 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14310927717/312500000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-8221/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c34 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-776659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6150351/10000000) (δ := 7011/500000000) (ψ := -182979/200000) 277 156
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t34 : ((-666022530537/5000000000000 : ℚ) : ℝ) ≤ stT277 34 := by
  have hc : ((-776709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-666022530537/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-776709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c35 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((755887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1784471/10000000) (δ := 6937/500000000) (ψ := -182979/200000) 277 157
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t35 : ((319399331949/2500000000000 : ℚ) : ℝ) ≤ stT277 35 := by
  have hc : ((755837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319399331949/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((755837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c36 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((346063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1007957/5000000) (δ := 13867/1000000000) (ψ := -182979/200000) 277 158
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t36 : ((144182442327/1250000000000 : ℚ) : ℝ) ≤ stT277 36 := by
  have hc : ((173019/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144182442327/1250000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((173019/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c37 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-515771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2640879/5000000) (δ := 349/25000000) (ψ := -182979/200000) 277 159
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t37 : ((-84800456579/1000000000000 : ℚ) : ℝ) ≤ stT277 37 := by
  have hc : ((-515821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84800456579/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-515821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c38 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-249297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -191661/250000) (δ := 6973/500000000) (ψ := -182979/200000) 277 161
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t38 : ((-161773444217/1000000000000 : ℚ) : ℝ) ≤ stT277 38 := by
  have hc : ((-498619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161773444217/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-498619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c39 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-275579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5386369/10000000) (δ := 2793/200000000) (ψ := -182979/200000) 277 162
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t39 : ((-55164965541/625000000000 : ℚ) : ℝ) ≤ stT277 39 := by
  have hc : ((-68901/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55164965541/625000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-68901/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c40 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((5823/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -890439/2500000) (δ := 867/62500000) (ψ := -182979/200000) 277 163
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t40 : ((4601902149/200000000000 : ℚ) : ℝ) ≤ stT277 40 := by
  have hc : ((5821/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4601902149/200000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((5821/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c41 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((25853/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1085047/5000000) (δ := 3481/250000000) (ψ := -182979/200000) 277 164
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t41 : ((40372463187/400000000000 : ℚ) : ℝ) ≤ stT277 41 := by
  have hc : ((25851/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40372463187/400000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((25851/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c42 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((888749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1190469/10000000) (δ := 6943/500000000) (ψ := -182979/200000) 277 165
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t42 : ((1371291884067/10000000000000 : ℚ) : ℝ) ≤ stT277 42 := by
  have hc : ((888699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1371291884067/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((888699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c43 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((485499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -603561/10000000) (δ := 13893/1000000000) (ψ := -182979/200000) 277 166
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t43 : ((74034056789/500000000000 : ℚ) : ℝ) ≤ stT277 43 := by
  have hc : ((242737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74034056789/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((242737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c44 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((15434/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3057/78125) (δ := 14003/1000000000) (ψ := -182979/200000) 277 167
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t44 : ((186131532207/1250000000000 : ℚ) : ℝ) ≤ stT277 44 := by
  have hc : ((493863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186131532207/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((493863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c45 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((122129/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -107369/2000000) (δ := 2779/200000000) (ψ := -182979/200000) 277 168
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t45 : ((728198907101/5000000000000 : ℚ) : ℝ) ≤ stT277 45 := by
  have hc : ((488491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((728198907101/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((488491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c46 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((917213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51221/500000) (δ := 217/15625000) (ψ := -182979/200000) 277 169
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t46 : ((1352282553297/10000000000000 : ℚ) : ℝ) ≤ stT277 46 := by
  have hc : ((917163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1352282553297/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((917163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c47 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((185339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -183927/1000000) (δ := 7011/500000000) (ψ := -182979/200000) 277 170
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t47 : ((540652627797/5000000000000 : ℚ) : ℝ) ≤ stT277 47 := by
  have hc : ((370653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540652627797/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((370653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c48 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((374349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1483877/5000000) (δ := 13929/1000000000) (ψ := -182979/200000) 277 171
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t48 : ((4322030553/80000000000 : ℚ) : ℝ) ≤ stT277 48 := by
  have hc : ((374299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4322030553/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((374299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c49 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-186867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4396921/10000000) (δ := 3509/250000000) (ψ := -182979/200000) 277 172
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t49 : ((-66756098131/2500000000000 : ℚ) : ℝ) ≤ stT277 49 := by
  have hc : ((-186917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66756098131/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-186917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c50 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-191883/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3057223/5000000) (δ := 13959/1000000000) (ψ := -182979/200000) 277 173
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t50 : ((-271381302637/2500000000000 : ℚ) : ℝ) ≤ stT277 50 := by
  have hc : ((-383791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271381302637/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-383791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c51 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-994797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1519771/2000000) (δ := 1743/125000000) (ψ := -182979/200000) 277 173
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t51 : ((-1393065352007/10000000000000 : ℚ) : ℝ) ≤ stT277 51 := by
  have hc : ((-994847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1393065352007/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-994847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c52 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-534887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2668963/5000000) (δ := 13951/1000000000) (ψ := -182979/200000) 277 174
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t52 : ((-741824419687/10000000000000 : ℚ) : ℝ) ≤ stT277 52 := by
  have hc : ((-534937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-741824419687/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-534937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c53 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((107041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2820841/10000000) (δ := 6929/500000000) (ψ := -182979/200000) 277 175
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t53 : ((58805953097/1000000000000 : ℚ) : ℝ) ≤ stT277 53 := by
  have hc : ((214057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58805953097/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((214057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c54 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((999739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57157/10000000) (δ := 2773/200000000) (ψ := -182979/200000) 277 176
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t54 : ((1360403782803/10000000000000 : ℚ) : ℝ) ≤ stT277 54 := by
  have hc : ((999689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1360403782803/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((999689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c55 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((191561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -588811/2000000) (δ := 14031/1000000000) (ψ := -182979/200000) 277 177
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t55 : ((16141684429/312500000000 : ℚ) : ℝ) ≤ stT277 55 := by
  have hc : ((11971/31250 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16141684429/312500000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((11971/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c56 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-391317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6174207/10000000) (δ := 1753/125000000) (ψ := -182979/200000) 277 178
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t56 : ((-261476526997/2500000000000 : ℚ) : ℝ) ≤ stT277 56 := by
  have hc : ((-195671/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261476526997/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-195671/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c57 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-189837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3041383/5000000) (δ := 1753/125000000) (ψ := -182979/200000) 277 178
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t57 : ((-502923855567/5000000000000 : ℚ) : ℝ) ≤ stT277 57 := by
  have hc : ((-379699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502923855567/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-379699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c58 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((567401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19349/80000) (δ := 13987/1000000000) (ψ := -182979/200000) 277 179
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t58 : ((93121021683/1250000000000 : ℚ) : ℝ) ≤ stT277 58 := by
  have hc : ((567351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93121021683/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((567351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c59 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((836141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1451467/10000000) (δ := 14009/1000000000) (ψ := -182979/200000) 277 180
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t59 : ((1088497675899/10000000000000 : ℚ) : ℝ) ≤ stT277 59 := by
  have hc : ((836091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1088497675899/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((836091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c60 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-119023/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5520513/10000000) (δ := 13901/1000000000) (ψ := -182979/200000) 277 181
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t60 : ((-30734201567/400000000000 : ℚ) : ℝ) ≤ stT277 60 := by
  have hc : ((-119033/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30734201567/400000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-119033/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c61 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-717087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5926027/10000000) (δ := 6951/500000000) (ψ := -182979/200000) 277 181
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t61 : ((-918199983553/10000000000000 : ℚ) : ℝ) ≤ stT277 61 := by
  have hc : ((-717137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-918199983553/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-717137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c62 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((83017/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73923/500000) (δ := 2779/200000000) (ψ := -182979/200000) 277 182
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t62 : ((26356330753/250000000000 : ℚ) : ℝ) ≤ stT277 62 := by
  have hc : ((20753/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26356330753/250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((20753/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c63 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((4783/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1574613/5000000) (δ := 2783/200000000) (ψ := -182979/200000) 277 183
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t63 : ((192800849311/5000000000000 : ℚ) : ℝ) ≤ stT277 63 := by
  have hc : ((153031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192800849311/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((153031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c64 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-999239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 969559/1250000) (δ := 2803/200000000) (ψ := -182979/200000) 277 183
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t64 : ((-1249112249289/10000000000000 : ℚ) : ℝ) ≤ stT277 64 := by
  have hc : ((-999289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1249112249289/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-999289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c65 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((88203/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2785167/10000000) (δ := 13923/1000000000) (ψ := -182979/200000) 277 184
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t65 : ((109389922971/2000000000000 : ℚ) : ℝ) ≤ stT277 65 := by
  have hc : ((88193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109389922971/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((88193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c66 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((589771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2350053/10000000) (δ := 13973/1000000000) (ψ := -182979/200000) 277 185
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t66 : ((362947917497/5000000000000 : ℚ) : ℝ) ≤ stT277 66 := by
  have hc : ((589721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362947917497/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((589721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c67 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-249121/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -764427/1000000) (δ := 13937/1000000000) (ψ := -182979/200000) 277 186
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t67 : ((-121746060513/1000000000000 : ℚ) : ℝ) ≤ stT277 67 := by
  have hc : ((-498267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121746060513/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-498267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c68 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((125243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2615187/10000000) (δ := 14037/1000000000) (ψ := -182979/200000) 277 186
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t68 : ((151864272279/2500000000000 : ℚ) : ℝ) ≤ stT277 68 := by
  have hc : ((250461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151864272279/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((250461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c69 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((368647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -745777/2500000) (δ := 13959/1000000000) (ψ := -182979/200000) 277 187
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t69 : ((221869223613/5000000000000 : ℚ) : ℝ) ≤ stT277 69 := by
  have hc : ((368597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221869223613/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((368597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c70 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-469829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6981067/10000000) (δ := 13859/1000000000) (ψ := -182979/200000) 277 187
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t70 : ((-280791563283/2500000000000 : ℚ) : ℝ) ≤ stT277 70 := by
  have hc : ((-234927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280791563283/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-234927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c71 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((452721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1095939/10000000) (δ := 109/7812500) (ψ := -182979/200000) 277 188
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t71 : ((67156376447/625000000000 : ℚ) : ℝ) ≤ stT277 71 := by
  have hc : ((56587/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67156376447/625000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((56587/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c72 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-194621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4926511/10000000) (δ := 6979/500000000) (ψ := -182979/200000) 277 189
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t72 : ((-7168520211/156250000000 : ℚ) : ℝ) ≤ stT277 72 := by
  have hc : ((-97323/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7168520211/156250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-97323/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c73 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-68931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4625349/10000000) (δ := 6929/500000000) (ψ := -182979/200000) 277 189
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t73 : ((-40346149861/1250000000000 : ℚ) : ℝ) ≤ stT277 73 := by
  have hc : ((-137887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40346149861/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-137887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c74 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((98419/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25949/156250) (δ := 6983/500000000) (ψ := -182979/200000) 277 190
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t74 : ((114402459969/1250000000000 : ℚ) : ℝ) ≤ stT277 74 := by
  have hc : ((393651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114402459969/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((393651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c75 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-498079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 190869/250000) (δ := 14037/1000000000) (ψ := -182979/200000) 277 190
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t75 : ((-71895148363/625000000000 : ℚ) : ℝ) ≤ stT277 75 := by
  have hc : ((-62263/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71895148363/625000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-62263/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c76 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((180981/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549549/5000000) (δ := 1393/100000000) (ψ := -182979/200000) 277 191
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t76 : ((103793926369/1000000000000 : ℚ) : ℝ) ≤ stT277 76 := by
  have hc : ((180971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103793926369/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((180971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c77 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-606601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1389109/2500000) (δ := 13923/1000000000) (ψ := -182979/200000) 277 192
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t77 : ((-345671559753/5000000000000 : ℚ) : ℝ) ≤ stT277 77 := by
  have hc : ((-606651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345671559753/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-606651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c78 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((217379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3379169/10000000) (δ := 699/50000000) (ψ := -182979/200000) 277 192
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t78 : ((246076628133/10000000000000 : ℚ) : ℝ) ≤ stT277 78 := by
  have hc : ((217329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246076628133/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((217329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c79 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((167193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3507037/10000000) (δ := 13887/1000000000) (ψ := -182979/200000) 277 193
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t79 : ((188050416441/10000000000000 : ℚ) : ℝ) ≤ stT277 79 := by
  have hc : ((167143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188050416441/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((167143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c80 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-244401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2601891/5000000) (δ := 13887/1000000000) (ψ := -182979/200000) 277 193
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t80 : ((-68319144621/1250000000000 : ℚ) : ℝ) ≤ stT277 80 := by
  have hc : ((-122213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68319144621/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-122213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c81 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((144879/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2377/12500) (δ := 6947/500000000) (ψ := -182979/200000) 277 194
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t81 : ((160965539459/2000000000000 : ℚ) : ℝ) ≤ stT277 81 := by
  have hc : ((144869/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160965539459/2000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((144869/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c82 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-43797/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1648861/2500000) (δ := 13909/1000000000) (ψ := -182979/200000) 277 194
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t82 : ((-24184244321/250000000000 : ℚ) : ℝ) ≤ stT277 82 := by
  have hc : ((-87599/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24184244321/250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-87599/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c83 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((95899/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14369/200000) (δ := 14001/1000000000) (ψ := -182979/200000) 277 195
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t83 : ((26314320487/250000000000 : ℚ) : ℝ) ≤ stT277 83 := by
  have hc : ((47947/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26314320487/250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((47947/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c84 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-496891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3787517/5000000) (δ := 27801/1000000000) (ψ := -182979/200000) 277 195
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t84 : ((-13554501961/125000000000 : ℚ) : ℝ) ≤ stT277 84 := by
  have hc : ((-124229/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13554501961/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-124229/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c85 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((124961/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15607/2500000) (δ := 14009/1000000000) (ψ := -182979/200000) 277 196
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t85 : ((135532419497/1250000000000 : ℚ) : ℝ) ≤ stT277 85 := by
  have hc : ((499819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135532419497/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((499819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c86 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-124053/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -943257/1250000) (δ := 13987/1000000000) (ψ := -182979/200000) 277 197
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t86 : ((-66888281467/625000000000 : ℚ) : ℝ) ≤ stT277 86 := by
  have hc : ((-496237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66888281467/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-496237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c87 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((983129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114967/2500000) (δ := 219/15625000) (ψ := -182979/200000) 277 197
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t87 : ((65873174553/625000000000 : ℚ) : ℝ) ≤ stT277 87 := by
  have hc : ((983079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65873174553/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((983079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c88 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-122303/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7333721/10000000) (δ := 347/25000000) (ψ := -182979/200000) 277 198
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t88 : ((-130382149737/1250000000000 : ℚ) : ℝ) ≤ stT277 88 := by
  have hc : ((-489237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130382149737/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-489237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c89 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((980761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 491183/10000000) (δ := 13923/1000000000) (ψ := -182979/200000) 277 198
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t89 : ((1039550717867/10000000000000 : ℚ) : ℝ) ≤ stT277 89 := by
  have hc : ((980711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1039550717867/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((980711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c90 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-247197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -747927/1000000) (δ := 1393/100000000) (ψ := -182979/200000) 277 199
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t90 : ((-521163606967/5000000000000 : ℚ) : ℝ) ≤ stT277 90 := by
  have hc : ((-494419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521163606967/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-494419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c91 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((498807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172751/10000000) (δ := 2773/100000000) (ψ := -182979/200000) 277 199
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t91 : ((65358148761/625000000000 : ℚ) : ℝ) ≤ stT277 91 := by
  have hc : ((249391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65358148761/625000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((249391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c92 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-998981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3870559/5000000) (δ := 13873/1000000000) (ψ := -182979/200000) 277 199
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t92 : ((-1041562746763/10000000000000 : ℚ) : ℝ) ≤ stT277 92 := by
  have hc : ((-999031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1041562746763/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-999031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c93 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((490801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -480297/10000000) (δ := 6933/500000000) (ψ := -182979/200000) 277 200
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t93 : ((63613832997/625000000000 : ℚ) : ℝ) ≤ stT277 93 := by
  have hc : ((61347/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63613832997/625000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((61347/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c94 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-232981/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3463099/5000000) (δ := 6983/500000000) (ψ := -182979/200000) 277 200
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t94 : ((-240314621757/2500000000000 : ℚ) : ℝ) ≤ stT277 94 := by
  have hc : ((-465987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240314621757/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-465987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c95 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((835659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1453661/10000000) (δ := 6979/500000000) (ψ := -182979/200000) 277 201
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t95 : ((428658225301/5000000000000 : ℚ) : ℝ) ≤ stT277 95 := by
  have hc : ((835609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428658225301/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((835609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c96 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-340193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1159543/2000000) (δ := 2809/200000000) (ψ := -182979/200000) 277 201
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t96 : ((-173616817689/2500000000000 : ℚ) : ℝ) ≤ stT277 96 := by
  have hc : ((-170109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173616817689/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-170109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c97 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((459287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -273401/1000000) (δ := 13951/1000000000) (ψ := -182979/200000) 277 202
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t97 : ((233142225501/5000000000000 : ℚ) : ℝ) ≤ stT277 97 := by
  have hc : ((459237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233142225501/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((459237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c98 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-175733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 546077/1250000) (δ := 14051/1000000000) (ψ := -182979/200000) 277 202
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t98 : ((-177567724799/10000000000000 : ℚ) : ℝ) ≤ stT277 98 := by
  have hc : ((-175783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177567724799/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-175783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c99 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-30427/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430881/1000000) (δ := 1743/125000000) (ψ := -182979/200000) 277 203
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t99 : ((-15295170803/1000000000000 : ℚ) : ℝ) ≤ stT277 99 := by
  have hc : ((-30437/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15295170803/1000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-30437/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c100 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((97703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2651023/10000000) (δ := 13859/1000000000) (ψ := -182979/200000) 277 203
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t100 : ((97692902307/2000000000000 : ℚ) : ℝ) ≤ stT277 100 := by
  have hc : ((97693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97692902307/2000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((97693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c101 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-780659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -385393/625000) (δ := 6983/500000000) (ψ := -182979/200000) 277 204
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t101 : ((-388417560971/5000000000000 : ℚ) : ℝ) ≤ stT277 101 := by
  have hc : ((-780709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388417560971/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-780709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c102 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((482863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 656429/10000000) (δ := 14037/1000000000) (ψ := -182979/200000) 277 204
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t102 : ((239040298593/2500000000000 : ℚ) : ℝ) ≤ stT277 102 := by
  have hc : ((241419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239040298593/2500000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((241419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c103 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-19689/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7412529/10000000) (δ := 6983/500000000) (ψ := -182979/200000) 277 204
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t103 : ((-194011477/2000000000 : ℚ) : ℝ) ≤ stT277 103 := by
  have hc : ((-1969/2000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194011477/2000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-1969/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c104 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((801003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1604569/10000000) (δ := 1393/100000000) (ψ := -182979/200000) 277 205
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t104 : ((39269924637/500000000000 : ℚ) : ℝ) ≤ stT277 104 := by
  have hc : ((800953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39269924637/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((800953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c105 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-84849/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502231/1000000) (δ := 13873/1000000000) (ψ := -182979/200000) 277 205
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t105 : ((-82813982959/2000000000000 : ℚ) : ℝ) ≤ stT277 105 := by
  have hc : ((-84859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82813982959/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-84859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c106 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-77787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2060827/5000000) (δ := 14023/1000000000) (ψ := -182979/200000) 277 206
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t106 : ((-37800994191/5000000000000 : ℚ) : ℝ) ≤ stT277 106 := by
  have hc : ((-77837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37800994191/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-77837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c107 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((2899/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2380783/10000000) (δ := 347/25000000) (ψ := -182979/200000) 277 206
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t107 : ((140116299/2500000000 : ℚ) : ℝ) ≤ stT277 107 := by
  have hc : ((2319/4000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140116299/2500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((2319/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c108 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-462931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1721317/2500000) (δ := 3497/250000000) (ψ := -182979/200000) 277 207
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t108 : ((-111369968489/1250000000000 : ℚ) : ℝ) ≤ stT277 108 := by
  have hc : ((-115739/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111369968489/1250000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-115739/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c109 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((489923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -502773/10000000) (δ := 2783/200000000) (ψ := -182979/200000) 277 207
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t109 : ((117309260437/1250000000000 : ℚ) : ℝ) ≤ stT277 109 := by
  have hc : ((244949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117309260437/1250000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((244949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c110 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-687323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5821483/10000000) (δ := 2803/200000000) (ψ := -182979/200000) 277 207
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t110 : ((-655384722699/10000000000000 : ℚ) : ℝ) ≤ stT277 110 := by
  have hc : ((-687373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-655384722699/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-687373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c111 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((122717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113107/312500) (δ := 2779/200000000) (ψ := -182979/200000) 277 208
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t111 : ((116430241719/10000000000000 : ℚ) : ℝ) ≤ stT277 111 := by
  have hc : ((122667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116430241719/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((122667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c112 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((63651/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2591331/10000000) (δ := 1751/125000000) (ψ := -182979/200000) 277 208
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t112 : ((240554497469/5000000000000 : ℚ) : ℝ) ≤ stT277 112 := by
  have hc : ((254579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240554497469/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((254579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c113 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-468441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6960999/10000000) (δ := 7001/500000000) (ψ := -182979/200000) 277 209
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t113 : ((-220347901993/2500000000000 : ℚ) : ℝ) ≤ stT277 113 := by
  have hc : ((-234233/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220347901993/2500000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-234233/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c114 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((941459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -859659/10000000) (δ := 13901/1000000000) (ψ := -182979/200000) 277 209
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t114 : ((176341909653/2000000000000 : ℚ) : ℝ) ≤ stT277 114 := by
  have hc : ((941409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176341909653/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((941409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c115 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-96687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1297107/2500000) (δ := 14001/1000000000) (ψ := -182979/200000) 277 209
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t115 : ((-18034087197/400000000000 : ℚ) : ℝ) ≤ stT277 115 := by
  have hc : ((-96697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18034087197/400000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-96697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c116 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-23649/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452387/1000000) (δ := 6947/500000000) (ψ := -182979/200000) 277 210
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t116 : ((-10981097479/500000000000 : ℚ) : ℝ) ≤ stT277 116 := by
  have hc : ((-11827/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10981097479/500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-11827/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c117 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((84289/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 355103/2500000) (δ := 14009/1000000000) (ψ := -182979/200000) 277 210
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t117 : ((38960279/500000000 : ℚ) : ℝ) ≤ stT277 117 := by
  have hc : ((21071/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38960279/500000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((21071/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c118 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-97677/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7314071/10000000) (δ := 6997/500000000) (ψ := -182979/200000) 277 210
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t118 : ((-1798472143/20000000000 : ℚ) : ℝ) ≤ stT277 118 := by
  have hc : ((-48841/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1798472143/20000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-48841/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c119 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((261679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2550023/10000000) (δ := 13887/1000000000) (ψ := -182979/200000) 277 211
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t119 : ((59964424623/1250000000000 : ℚ) : ℝ) ≤ stT277 119 := by
  have hc : ((130827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59964424623/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((130827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c120 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((33677/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129801/400000) (δ := 3479/250000000) (ψ := -182979/200000) 277 211
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t120 : ((12294807021/500000000000 : ℚ) : ℝ) ≤ stT277 120 := by
  have hc : ((134683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12294807021/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((134683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c121 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-44909/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6716019/10000000) (δ := 1753/125000000) (ψ := -182979/200000) 277 212
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t121 : ((-81657280893/1000000000000 : ℚ) : ℝ) ≤ stT277 121 := by
  have hc : ((-89823/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81657280893/1000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-89823/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c122 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((918487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -508199/5000000) (δ := 3481/250000000) (ψ := -182979/200000) 277 212
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t122 : ((831513367009/10000000000000 : ℚ) : ℝ) ≤ stT277 122 := by
  have hc : ((918437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((831513367009/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((918437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c123 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-280081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4636687/10000000) (δ := 13879/1000000000) (ψ := -182979/200000) 277 212
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t123 : ((-25258571877/1000000000000 : ℚ) : ℝ) ≤ stT277 123 := by
  have hc : ((-280131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25258571877/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-280131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c124 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-576787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1092793/2000000) (δ := 13931/1000000000) (ψ := -182979/200000) 277 213
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t124 : ((-518015200599/10000000000000 : ℚ) : ℝ) ≤ stT277 124 := by
  have hc : ((-576837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518015200599/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-576837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c125 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((999227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98333/10000000) (δ := 3493/250000000) (ψ := -182979/200000) 277 213
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t125 : ((893690886579/10000000000000 : ℚ) : ℝ) ≤ stT277 125 := by
  have hc : ((999177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((893690886579/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((999177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c126 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-312733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 702039/1250000) (δ := 13931/1000000000) (ψ := -182979/200000) 277 213
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t126 : ((-139313516109/2500000000000 : ℚ) : ℝ) ≤ stT277 126 := by
  have hc : ((-156379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139313516109/2500000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-156379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c127 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-54531/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461737/1000000) (δ := 2793/200000000) (ψ := -182979/200000) 277 214
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t127 : ((-48397338137/2000000000000 : ℚ) : ℝ) ≤ stT277 127 := by
  have hc : ((-54541/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48397338137/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-54541/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c128 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((947453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 407023/5000000) (δ := 2793/200000000) (ψ := -182979/200000) 277 214
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t128 : ((837393405849/10000000000000 : ℚ) : ℝ) ≤ stT277 128 := by
  have hc : ((947403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((837393405849/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((947403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c129 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-157961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310161/500000) (δ := 6969/500000000) (ψ := -182979/200000) 277 214
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t129 : ((-139085724921/2000000000000 : ℚ) : ℝ) ≤ stT277 129 := by
  have hc : ((-157971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139085724921/2000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-157971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c130 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-91977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2078629/5000000) (δ := 2809/200000000) (ψ := -182979/200000) 277 215
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t130 : ((-80713108593/10000000000000 : ℚ) : ℝ) ≤ stT277 130 := by
  have hc : ((-92027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80713108593/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-92027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c131 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((896177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11493/100000) (δ := 2789/200000000) (ψ := -182979/200000) 277 215
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t131 : ((97868718051/1250000000000 : ℚ) : ℝ) ≤ stT277 131 := by
  have hc : ((896127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97868718051/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((896127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c132 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-33559/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1283097/2000000) (δ := 6979/500000000) (ψ := -182979/200000) 277 215
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t132 : ((-29211125229/400000000000 : ℚ) : ℝ) ≤ stT277 132 := by
  have hc : ((-33561/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29211125229/400000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-33561/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c133 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-6949/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2033021/5000000) (δ := 3463/250000000) (ψ := -182979/200000) 277 216
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t133 : ((-2412386731/500000000000 : ℚ) : ℝ) ≤ stT277 133 := by
  have hc : ((-27821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2412386731/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-27821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c134 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((901101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1121233/10000000) (δ := 27751/1000000000) (ψ := -182979/200000) 277 216
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t134 : ((194597281317/2500000000000 : ℚ) : ℝ) ≤ stT277 134 := by
  have hc : ((901051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194597281317/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((901051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c135 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-805891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391871/625000) (δ := 3463/250000000) (ψ := -182979/200000) 277 216
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t135 : ((-693643598883/10000000000000 : ℚ) : ℝ) ≤ stT277 135 := by
  have hc : ((-805941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-693643598883/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-805941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c136 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-159443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1081827/2500000) (δ := 13859/1000000000) (ψ := -182979/200000) 277 217
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t136 : ((-136764131049/10000000000000 : ℚ) : ℝ) ≤ stT277 136 := by
  have hc : ((-159493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136764131049/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-159493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c137 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((477903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23313/312500) (δ := 1743/125000000) (ψ := -182979/200000) 277 217
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t137 : ((204139207223/2500000000000 : ℚ) : ℝ) ≤ stT277 137 := by
  have hc : ((238939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204139207223/2500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((238939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c138 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-675873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5782361/10000000) (δ := 13859/1000000000) (ψ := -182979/200000) 277 217
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t138 : ((-575384185211/10000000000000 : ℚ) : ℝ) ≤ stT277 138 := by
  have hc : ((-675923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575384185211/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-675923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c139 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-194443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -985109/2000000) (δ := 3509/250000000) (ψ := -182979/200000) 277 218
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t139 : ((-41236404613/1250000000000 : ℚ) : ℝ) ≤ stT277 139 := by
  have hc : ((-48617/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41236404613/1250000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-48617/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c140 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((999881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19321/5000000) (δ := 13967/1000000000) (ψ := -182979/200000) 277 218
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t140 : ((422505584487/5000000000000 : ℚ) : ℝ) ≤ stT277 140 := by
  have hc : ((999831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422505584487/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((999831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c141 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-40427/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4967441/10000000) (δ := 871/62500000) (ψ := -182979/200000) 277 218
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t141 : ((-266014763/7812500000 : ℚ) : ℝ) ≤ stT277 141 := by
  have hc : ((-2527/6250 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266014763/7812500000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-2527/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c142 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-694553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2923243/5000000) (δ := 6937/500000000) (ψ := -182979/200000) 277 219
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t142 : ((-291449167373/5000000000000 : ℚ) : ℝ) ≤ stT277 142 := by
  have hc : ((-694603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291449167373/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-694603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c143 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((184621/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493399/5000000) (δ := 6937/500000000) (ψ := -182979/200000) 277 219
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t143 : ((77189735931/1000000000000 : ℚ) : ℝ) ≤ stT277 143 := by
  have hc : ((184611/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77189735931/1000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((184611/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c144 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((17603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3838957/10000000) (δ := 14029/1000000000) (ψ := -182979/200000) 277 219
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t144 : ((7324163737/2500000000000 : ℚ) : ℝ) ≤ stT277 144 := by
  have hc : ((8789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7324163737/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((8789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c145 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-476019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88457/125000) (δ := 7011/500000000) (ψ := -182979/200000) 277 220
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t145 : ((-19766656001/250000000000 : ℚ) : ℝ) ≤ stT277 145 := by
  have hc : ((-119011/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19766656001/250000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-119011/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c146 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((150093/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579269/2500000) (δ := 13981/1000000000) (ψ := -182979/200000) 277 220
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t146 : ((49682948881/1000000000000 : ℚ) : ℝ) ≤ stT277 146 := by
  have hc : ((300161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49682948881/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((300161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c147 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((114057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2409859/10000000) (δ := 7011/500000000) (ψ := -182979/200000) 277 220
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t147 : ((47032184471/1000000000000 : ℚ) : ℝ) ≤ stT277 147 := by
  have hc : ((114047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47032184471/1000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((114047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c148 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-955433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3552401/5000000) (δ := 13981/1000000000) (ψ := -182979/200000) 277 220
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t148 : ((-157080449717/2000000000000 : ℚ) : ℝ) ≤ stT277 148 := by
  have hc : ((-955483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157080449717/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-955483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c149 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-2561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3939797/10000000) (δ := 3497/250000000) (ψ := -182979/200000) 277 221
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t149 : ((-33102093/78125000000 : ℚ) : ℝ) ≤ stT277 149 := by
  have hc : ((-1293/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33102093/78125000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-1293/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c150 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((480953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 346133/5000000) (δ := 217/15625000) (ψ := -182979/200000) 277 221
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t150 : ((766944899/9765625000 : ℚ) : ℝ) ≤ stT277 150 := by
  have hc : ((15029/15625 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((766944899/9765625000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((15029/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c151 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-3249/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5293651/10000000) (δ := 2803/200000000) (ψ := -182979/200000) 277 221
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t151 : ((-42308076321/1000000000000 : ℚ) : ℝ) ≤ stT277 151 := by
  have hc : ((-51989/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42308076321/1000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-51989/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c152 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-693643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5843327/10000000) (δ := 2779/200000000) (ψ := -182979/200000) 277 222
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t152 : ((-140664985461/2500000000000 : ℚ) : ℝ) ≤ stT277 152 := by
  have hc : ((-693693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140664985461/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-693693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c153 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((216839/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162791/1250000) (δ := 1751/125000000) (ψ := -182979/200000) 277 222
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t153 : ((87646908789/1250000000000 : ℚ) : ℝ) ≤ stT277 153 := by
  have hc : ((433653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87646908789/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((433653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c154 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((11329/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1604551/5000000) (δ := 3477/250000000) (ψ := -182979/200000) 277 222
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t154 : ((4563772897/200000000000 : ℚ) : ℝ) ≤ stT277 154 := by
  have hc : ((11327/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4563772897/200000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((11327/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c155 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-249471/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1922827/2500000) (δ := 1751/125000000) (ψ := -182979/200000) 277 222
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t155 : ((-20039013687/250000000000 : ℚ) : ℝ) ≤ stT277 155 := by
  have hc : ((-498967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20039013687/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-498967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c156 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((144981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3563257/10000000) (δ := 7/500000) (ψ := -182979/200000) 277 223
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t156 : ((181308681/15625000000 : ℚ) : ℝ) ≤ stT277 156 := by
  have hc : ((144931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181308681/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((144931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c157 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((470593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10771/125000) (δ := 13903/1000000000) (ψ := -182979/200000) 277 223
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t157 : ((23472108303/312500000000 : ℚ) : ℝ) ≤ stT277 157 := by
  have hc : ((58821/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23472108303/312500000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((58821/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c158 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-253889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5258501/10000000) (δ := 13903/1000000000) (ψ := -182979/200000) 277 223
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t158 : ((-50500828503/1250000000000 : ℚ) : ℝ) ≤ stT277 158 := by
  have hc : ((-126957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50500828503/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-126957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c159 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-189679/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6080341/10000000) (δ := 1401/100000000) (ψ := -182979/200000) 277 224
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t159 : ((-75217611729/1250000000000 : ℚ) : ℝ) ≤ stT277 159 := by
  have hc : ((-379383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75217611729/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-379383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c160 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((767761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1738643/10000000) (δ := 1401/100000000) (ψ := -182979/200000) 277 224
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t160 : ((606928517559/10000000000000 : ℚ) : ℝ) ≤ stT277 160 := by
  have hc : ((767711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606928517559/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((767711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c161 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((514483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1287989/5000000) (δ := 1391/100000000) (ψ := -182979/200000) 277 224
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t161 : ((40542979163/1000000000000 : ℚ) : ℝ) ≤ stT277 161 := by
  have hc : ((514433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40542979163/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((514433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c162 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-184521/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3431969/5000000) (δ := 1391/100000000) (ψ := -182979/200000) 277 224
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t162 : ((-5799255737/80000000000 : ℚ) : ℝ) ≤ stT277 162 := by
  have hc : ((-184531/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5799255737/80000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-184531/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c163 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-25919/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91649/200000) (δ := 6993/500000000) (ψ := -182979/200000) 277 225
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t163 : ((-5076314541/250000000000 : ℚ) : ℝ) ≤ stT277 163 := by
  have hc : ((-6481/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5076314541/250000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-6481/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c164 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((61899/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -346981/10000000) (δ := 13917/1000000000) (ψ := -182979/200000) 277 225
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t164 : ((96665016239/1250000000000 : ℚ) : ℝ) ≤ stT277 164 := by
  have hc : ((495167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96665016239/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((495167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c165 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((25703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1931363/5000000) (δ := 6993/500000000) (ψ := -182979/200000) 277 225
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t165 : ((9985404597/5000000000000 : ℚ) : ℝ) ≤ stT277 165 := by
  have hc : ((25653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9985404597/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((25653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c166 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-49851/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478809/625000) (δ := 3481/250000000) (ψ := -182979/200000) 277 226
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t166 : ((-77387687757/1000000000000 : ℚ) : ℝ) ≤ stT277 166 := by
  have hc : ((-99707/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77387687757/1000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-99707/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c167 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((169289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87543/250000) (δ := 13879/1000000000) (ψ := -182979/200000) 277 226
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t167 : ((130961030697/10000000000000 : ℚ) : ℝ) ≤ stT277 167 := by
  have hc : ((169239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130961030697/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((169239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c168 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((484079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316287/5000000) (δ := 13979/1000000000) (ψ := -182979/200000) 277 226
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t168 : ((46681925733/625000000000 : ℚ) : ℝ) ≤ stT277 168 := by
  have hc : ((242027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46681925733/625000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((242027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c169 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-16021/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4742423/10000000) (δ := 13979/1000000000) (ψ := -182979/200000) 277 226
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t169 : ((-24651545857/1000000000000 : ℚ) : ℝ) ≤ stT277 169 := by
  have hc : ((-32047/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24651545857/1000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-32047/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c170 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-115633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3439999/5000000) (δ := 3493/250000000) (ψ := -182979/200000) 277 227
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t170 : ((-70953005901/1000000000000 : ℚ) : ℝ) ≤ stT277 170 := by
  have hc : ((-462557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70953005901/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-462557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c171 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((5363/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176151/625000) (δ := 867/62500000) (ψ := -182979/200000) 277 227
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t171 : ((32805680381/1000000000000 : ℚ) : ℝ) ≤ stT277 171 := by
  have hc : ((42899/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32805680381/1000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((42899/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c172 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((883369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609741/5000000) (δ := 3493/250000000) (ψ := -182979/200000) 277 227
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t172 : ((168380917737/2500000000000 : ℚ) : ℝ) ≤ stT277 172 := by
  have hc : ((883319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168380917737/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((883319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c173 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-249651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2616987/5000000) (δ := 867/62500000) (ψ := -182979/200000) 277 227
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t173 : ((-23728145917/625000000000 : ℚ) : ℝ) ≤ stT277 173 := by
  have hc : ((-62419/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23728145917/625000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-62419/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c174 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-426643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6482627/10000000) (δ := 2773/200000000) (ψ := -182979/200000) 277 228
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t174 : ((-80864146033/1250000000000 : ℚ) : ℝ) ≤ stT277 174 := by
  have hc : ((-106667/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80864146033/1250000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-106667/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c175 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((267771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2514117/10000000) (δ := 6969/500000000) (ψ := -182979/200000) 277 228
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t175 : ((12649793643/312500000000 : ℚ) : ℝ) ≤ stT277 175 := by
  have hc : ((133873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12649793643/312500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((133873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c176 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((840441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357937/2500000) (δ := 6969/500000000) (ψ := -182979/200000) 277 228
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t176 : ((316734123599/5000000000000 : ℚ) : ℝ) ≤ stT277 176 := by
  have hc : ((840391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316734123599/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((840391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c177 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-540751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2677657/5000000) (δ := 2793/200000000) (ψ := -182979/200000) 277 228
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t177 : ((-406491449247/10000000000000 : ℚ) : ℝ) ≤ stT277 177 := by
  have hc : ((-540801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406491449247/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-540801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c178 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-846673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3225621/5000000) (δ := 7023/500000000) (ψ := -182979/200000) 277 229
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t178 : ((-158661495909/2500000000000 : ℚ) : ℝ) ≤ stT277 178 := by
  have hc : ((-846723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158661495909/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-846723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c179 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((515967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51433/200000) (δ := 13957/1000000000) (ψ := -182979/200000) 277 229
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t179 : ((77122884579/2000000000000 : ℚ) : ℝ) ≤ stT277 179 := by
  have hc : ((515917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77122884579/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((515917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c180 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((174107/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321567/2500000) (δ := 6973/500000000) (ψ := -182979/200000) 277 229
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t180 : ((25952813887/400000000000 : ℚ) : ℝ) ≤ stT277 180 := by
  have hc : ((174097/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25952813887/400000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((174097/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c181 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-57539/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 640357/1250000) (δ := 13957/1000000000) (ψ := -182979/200000) 277 229
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t181 : ((-34218477279/1000000000000 : ℚ) : ℝ) ≤ stT277 181 := by
  have hc : ((-230181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34218477279/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-230181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c182 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-907413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6769709/10000000) (δ := 13853/1000000000) (ψ := -182979/200000) 277 230
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t182 : ((-538125559/8000000000 : ℚ) : ℝ) ≤ stT277 182 := by
  have hc : ((-907463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538125559/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-907463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c183 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((185801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595031/2000000) (δ := 13953/1000000000) (ψ := -182979/200000) 277 230
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t183 : ((8583095031/312500000000 : ℚ) : ℝ) ≤ stT277 183 := by
  have hc : ((11611/31250 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8583095031/312500000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((11611/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c184 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((4747/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 798693/10000000) (δ := 13953/1000000000) (ψ := -182979/200000) 277 230
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t184 : ((13997387283/200000000000 : ℚ) : ℝ) ≤ stT277 184 := by
  have hc : ((18987/20000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13997387283/200000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((18987/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c185 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-247451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284507/625000) (δ := 13853/1000000000) (ψ := -182979/200000) 277 230
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t185 : ((-36393289543/2000000000000 : ℚ) : ℝ) ≤ stT277 185 := by
  have hc : ((-247501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36393289543/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-247501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c186 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-492579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3711361/5000000) (δ := 349/25000000) (ψ := -182979/200000) 277 231
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t186 : ((-22574686659/312500000000 : ℚ) : ℝ) ≤ stT277 186 := by
  have hc : ((-123151/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22574686659/312500000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-123151/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c187 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((10859/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3709537/10000000) (δ := 349/25000000) (ψ := -182979/200000) 277 231
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t187 : ((3968156099/625000000000 : ℚ) : ℝ) ≤ stT277 187 := by
  have hc : ((43411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3968156099/625000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((43411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c188 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((999979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16227/10000000) (δ := 693/50000000) (ψ := -182979/200000) 277 231
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t188 : ((182318054499/2500000000000 : ℚ) : ℝ) ≤ stT277 188 := by
  have hc : ((999929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182318054499/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((999929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c189 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((53783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731511/2000000) (δ := 349/25000000) (ψ := -182979/200000) 277 231
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t189 : ((610986549/78125000000 : ℚ) : ℝ) ≤ stT277 189 := by
  have hc : ((26879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((610986549/78125000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((26879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c190 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-488291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7311877/10000000) (δ := 13943/1000000000) (ψ := -182979/200000) 277 231
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t190 : ((-88565506683/1250000000000 : ℚ) : ℝ) ≤ stT277 190 := by
  have hc : ((-122079/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88565506683/1250000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-122079/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c191 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-81851/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4760877/10000000) (δ := 3509/250000000) (ψ := -182979/200000) 277 232
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t191 : ((-4738750561/200000000000 : ℚ) : ℝ) ≤ stT277 191 := by
  have hc : ((-163727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4738750561/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-163727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c192 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((89699/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1144711/10000000) (δ := 871/62500000) (ψ := -182979/200000) 277 232
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t192 : ((32365496889/500000000000 : ℚ) : ℝ) ≤ stT277 192 := by
  have hc : ((44847/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32365496889/500000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((44847/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c193 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((556129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153293/625000) (δ := 871/62500000) (ψ := -182979/200000) 277 232
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t193 : ((80054801077/2000000000000 : ℚ) : ℝ) ≤ stT277 193 := by
  have hc : ((556079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80054801077/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((556079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c194 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-745853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 753941/1250000) (δ := 871/62500000) (ψ := -182979/200000) 277 232
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t194 : ((-535527771977/10000000000000 : ℚ) : ℝ) ≤ stT277 194 := by
  have hc : ((-745903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-535527771977/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-745903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c195 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-383967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382251/625000) (δ := 14029/1000000000) (ψ := -182979/200000) 277 233
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t195 : ((-6874560777/125000000000 : ℚ) : ℝ) ≤ stT277 195 := by
  have hc : ((-47999/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6874560777/125000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-47999/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c196 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((515227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2573809/10000000) (δ := 13929/1000000000) (ψ := -182979/200000) 277 233
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t196 : ((73596640689/2000000000000 : ℚ) : ℝ) ≤ stT277 196 := by
  have hc : ((515177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73596640689/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((515177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c197 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((464303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 950393/10000000) (δ := 6937/500000000) (ψ := -182979/200000) 277 233
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t197 : ((16539207333/250000000000 : ℚ) : ℝ) ≤ stT277 197 := by
  have hc : ((232139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16539207333/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((232139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c198 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-210313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 557091/1250000) (δ := 13929/1000000000) (ψ := -182979/200000) 277 233
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t198 : ((-14949867321/1000000000000 : ℚ) : ℝ) ≤ stT277 198 := by
  have hc : ((-210363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14949867321/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-210363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c199 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-999331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7762559/10000000) (δ := 14021/1000000000) (ψ := -182979/200000) 277 234
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t199 : ((-354221601021/5000000000000 : ℚ) : ℝ) ≤ stT277 199 := by
  have hc : ((-999381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354221601021/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-999381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c200 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-145249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2145701/5000000) (δ := 6991/500000000) (ψ := -182979/200000) 277 234
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t200 : ((-102741939993/10000000000000 : ℚ) : ℝ) ≤ stT277 200 := by
  have hc : ((-145299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102741939993/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-145299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c201 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((236103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837489/10000000) (δ := 6991/500000000) (ψ := -182979/200000) 277 234
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t201 : ((66610101489/1000000000000 : ℚ) : ℝ) ≤ stT277 201 := by
  have hc : ((472181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66610101489/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((472181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c202 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((506503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129959/500000) (δ := 14021/1000000000) (ψ := -182979/200000) 277 234
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t202 : ((356338811441/10000000000000 : ℚ) : ℝ) ≤ stT277 202 := by
  have hc : ((506453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356338811441/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((506453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c203 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-742493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6018953/10000000) (δ := 13921/1000000000) (ψ := -182979/200000) 277 234
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t203 : ((-521163457609/10000000000000 : ℚ) : ℝ) ≤ stT277 203 := by
  have hc : ((-742543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521163457609/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-742543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c204 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-404847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257213/2000000) (δ := 13889/1000000000) (ψ := -182979/200000) 277 235
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t204 : ((-35433435869/625000000000 : ℚ) : ℝ) ≤ stT277 204 := by
  have hc : ((-50609/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35433435869/625000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-50609/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c205 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((79887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144987/500000) (δ := 13889/1000000000) (ψ := -182979/200000) 277 235
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t205 : ((5578849311/200000000000 : ℚ) : ℝ) ≤ stT277 205 := by
  have hc : ((79877/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5578849311/200000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((79877/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c206 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((245593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 470103/10000000) (δ := 7007/500000000) (ψ := -182979/200000) 277 235
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t206 : ((342208077013/5000000000000 : ℚ) : ℝ) ≤ stT277 206 := by
  have hc : ((491161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342208077013/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((491161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c207 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((41343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955901/2500000) (δ := 13889/1000000000) (ψ := -182979/200000) 277 235
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t207 : ((3587577133/1250000000000 : ℚ) : ℝ) ≤ stT277 207 := by
  have hc : ((41293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3587577133/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((41293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c208 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-30057/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7160969/10000000) (δ := 6957/500000000) (ψ := -182979/200000) 277 235
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t208 : ((-2605235729/39062500000 : ℚ) : ℝ) ≤ stT277 208 := by
  have hc : ((-480937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2605235729/39062500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-480937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c209 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-248203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2612813/5000000) (δ := 14007/1000000000) (ψ := -182979/200000) 277 236
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t209 : ((-8585151551/250000000000 : ℚ) : ℝ) ≤ stT277 209 := by
  have hc : ((-62057/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8585151551/250000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-62057/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c210 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((71927/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -384023/2000000) (δ := 3499/250000000) (ψ := -182979/200000) 277 236
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t210 : ((4963085493/100000000000 : ℚ) : ℝ) ≤ stT277 210 := by
  have hc : ((35961/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4963085493/100000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((35961/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c211 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((213409/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54787/400000) (δ := 13907/1000000000) (ψ := -182979/200000) 277 236
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t211 : ((73454062851/1250000000000 : ℚ) : ℝ) ≤ stT277 211 := by
  have hc : ((426793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73454062851/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((426793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c212 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-282843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1160971/2500000) (δ := 14007/1000000000) (ψ := -182979/200000) 277 236
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t212 : ((-194291761079/10000000000000 : ℚ) : ℝ) ≤ stT277 212 := by
  have hc : ((-282893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194291761079/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-282893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c213 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-99981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7805243/10000000) (δ := 13903/1000000000) (ψ := -182979/200000) 277 237
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t213 : ((-34254653677/500000000000 : ℚ) : ℝ) ≤ stT277 213 := by
  have hc : ((-49993/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34254653677/500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-49993/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c214 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-251143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2280821/5000000) (δ := 14003/1000000000) (ψ := -182979/200000) 277 237
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t214 : ((-85856009049/5000000000000 : ℚ) : ℝ) ≤ stT277 214 := by
  have hc : ((-251193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85856009049/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-251193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c215 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((861143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1333207/10000000) (δ := 14003/1000000000) (ψ := -182979/200000) 277 237
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t215 : ((293630129721/5000000000000 : ℚ) : ℝ) ≤ stT277 215 := by
  have hc : ((861093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293630129721/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((861093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c216 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((2921/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188027/1000000) (δ := 14003/1000000000) (ψ := -182979/200000) 277 237
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t216 : ((2484187863/50000000000 : ℚ) : ℝ) ≤ stT277 216 := by
  have hc : ((3651/5000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2484187863/50000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((3651/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c217 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-444617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2539429/5000000) (δ := 13903/1000000000) (ψ := -182979/200000) 277 237
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t217 : ((-60371993923/2000000000000 : ℚ) : ℝ) ≤ stT277 217 := by
  have hc : ((-444667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60371993923/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-444667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c218 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-986661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3722599/5000000) (δ := 1391/100000000) (ψ := -182979/200000) 277 238
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t218 : ((-334142773173/5000000000000 : ℚ) : ℝ) ≤ stT277 218 := by
  have hc : ((-986711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334142773173/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-986711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c219 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-27817/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4275833/10000000) (δ := 1401/100000000) (ψ := -182979/200000) 277 238
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t219 : ((-9401880663/1000000000000 : ℚ) : ℝ) ≤ stT277 219 := by
  have hc : ((-27827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9401880663/1000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-27827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c220 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((28161/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -560471/5000000) (δ := 13893/1000000000) (ψ := -182979/200000) 277 238
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t220 : ((303761033649/5000000000000 : ℚ) : ℝ) ≤ stT277 220 := by
  have hc : ((450551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303761033649/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((450551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c221 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((691037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504921/2500000) (δ := 13893/1000000000) (ψ := -182979/200000) 277 238
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t221 : ((14525237727/312500000000 : ℚ) : ℝ) ≤ stT277 221 := by
  have hc : ((690987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14525237727/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((690987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c222 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-234263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1029209/2000000) (δ := 1401/100000000) (ψ := -182979/200000) 277 238
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t222 : ((-9827751951/312500000000 : ℚ) : ℝ) ≤ stT277 222 := by
  have hc : ((-14643/31250 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9827751951/312500000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-14643/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c223 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-986943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7449547/10000000) (δ := 6993/500000000) (ψ := -182979/200000) 277 239
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t223 : ((-13218797249/200000000000 : ℚ) : ℝ) ≤ stT277 223 := by
  have hc : ((-986993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13218797249/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-986993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c224 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-168829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2175547/5000000) (δ := 6943/500000000) (ψ := -182979/200000) 277 239
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t224 : ((-56418589683/5000000000000 : ℚ) : ℝ) ≤ stT277 224 := by
  have hc : ((-168879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56418589683/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-168879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c225 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((437207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -633211/5000000) (δ := 6943/500000000) (ψ := -182979/200000) 277 239
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t225 : ((72863593803/1250000000000 : ℚ) : ℝ) ≤ stT277 225 := by
  have hc : ((218591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72863593803/1250000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((218591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c226 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((750617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 225563/1250000) (δ := 27717/1000000000) (ψ := -182979/200000) 277 239
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t226 : ((49926966273/1000000000000 : ℚ) : ℝ) ≤ stT277 226 := by
  have hc : ((750567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49926966273/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((750567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c227 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-182659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2430963/5000000) (δ := 6943/500000000) (ψ := -182979/200000) 277 239
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t227 : ((-7578234701/312500000000 : ℚ) : ℝ) ≤ stT277 227 := by
  have hc : ((-45671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7578234701/312500000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-45671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c228 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-199957/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1950521/2500000) (δ := 557/40000000) (ψ := -182979/200000) 277 240
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t228 : ((-132431545189/2000000000000 : ℚ) : ℝ) ≤ stT277 228 := by
  have hc : ((-199967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132431545189/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-199967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c229 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-82847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4771427/10000000) (δ := 557/40000000) (ψ := -182979/200000) 277 240
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t229 : ((-109510263861/5000000000000 : ℚ) : ℝ) ≤ stT277 229 := by
  have hc : ((-165719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109510263861/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-165719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c230 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((763811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1753997/10000000) (δ := 6939/500000000) (ψ := -182979/200000) 277 240
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t230 : ((25180436409/500000000000 : ℚ) : ℝ) ≤ stT277 230 := by
  have hc : ((763761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25180436409/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((763761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c231 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((219379/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250069/2000000) (δ := 6939/500000000) (ψ := -182979/200000) 277 240
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t231 : ((288664816083/5000000000000 : ℚ) : ℝ) ≤ stT277 231 := by
  have hc : ((438733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((288664816083/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((438733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c232 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-125539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1060417/2500000) (δ := 6939/500000000) (ψ := -182979/200000) 277 240
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t232 : ((-82453322937/10000000000000 : ℚ) : ℝ) ≤ stT277 232 := by
  have hc : ((-125589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82453322937/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-125589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c233 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-193607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 361009/500000) (δ := 557/40000000) (ψ := -182979/200000) 277 240
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t233 : ((-63421378137/1000000000000 : ℚ) : ℝ) ≤ stT277 233 := by
  have hc : ((-193617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63421378137/1000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-193617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c234 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-297799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2761007/5000000) (δ := 13971/1000000000) (ψ := -182979/200000) 277 241
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t234 : ((-6084181347/156250000000 : ℚ) : ℝ) ≤ stT277 234 := by
  have hc : ((-9307/15625 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6084181347/156250000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-9307/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c235 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((516903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2568917/10000000) (δ := 13971/1000000000) (ψ := -182979/200000) 277 241
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t235 : ((42144710473/1250000000000 : ℚ) : ℝ) ≤ stT277 235 := by
  have hc : ((516853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42144710473/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((516853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c236 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((988971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185823/5000000) (δ := 13871/1000000000) (ψ := -182979/200000) 277 241
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t236 : ((10058315491/156250000000 : ℚ) : ℝ) ≤ stT277 236 := by
  have hc : ((988921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10058315491/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((988921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c237 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((9931/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103117/312500) (δ := 3483/250000000) (ψ := -182979/200000) 277 241
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t237 : ((6449570601/400000000000 : ℚ) : ℝ) ≤ stT277 237 := by
  have hc : ((9929/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6449570601/400000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((9929/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c238 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-198203/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1243103/2000000) (δ := 13871/1000000000) (ψ := -182979/200000) 277 241
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t238 : ((-64242039981/1250000000000 : ℚ) : ℝ) ≤ stT277 238 := by
  have hc : ((-396431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64242039981/1250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-396431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c239 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-218667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1317773/2000000) (δ := 1733/125000000) (ψ := -182979/200000) 277 242
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t239 : ((-282904357073/5000000000000 : ℚ) : ℝ) ≤ stT277 239 := by
  have hc : ((-437359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282904357073/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-437359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c240 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((91707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18487/50000) (δ := 14039/1000000000) (ψ := -182979/200000) 277 242
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t240 : ((59164318529/10000000000000 : ℚ) : ℝ) ≤ stT277 240 := by
  have hc : ((91657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59164318529/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((91657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c241 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((236737/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163597/2000000) (δ := 14039/1000000000) (ψ := -182979/200000) 277 242
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t241 : ((76243753511/1250000000000 : ℚ) : ℝ) ≤ stT277 241 := by
  have hc : ((473449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76243753511/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((473449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c242 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((341181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2049519/10000000) (δ := 14039/1000000000) (ψ := -182979/200000) 277 242
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t242 : ((6853227017/156250000000 : ℚ) : ℝ) ≤ stT277 242 := by
  have hc : ((85289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6853227017/156250000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((85289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c243 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-47671/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4905181/10000000) (δ := 13939/1000000000) (ψ := -182979/200000) 277 242
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t243 : ((-122340014209/5000000000000 : ℚ) : ℝ) ≤ stT277 243 := by
  have hc : ((-190709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122340014209/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-190709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c244 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-999121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 387457/500000) (δ := 13939/1000000000) (ψ := -182979/200000) 277 242
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t244 : ((-127930857327/2000000000000 : ℚ) : ℝ) ≤ stT277 244 := by
  have hc : ((-999171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127930857327/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-999171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c245 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-461617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5126533/10000000) (δ := 13873/500000000) (ψ := -182979/200000) 277 243
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t245 : ((-294948427959/10000000000000 : ℚ) : ℝ) ≤ stT277 245 := by
  have hc : ((-461667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294948427959/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-461667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c246 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((75499/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1152869/5000000) (δ := 6973/500000000) (ψ := -182979/200000) 277 243
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t246 : ((24066182787/625000000000 : ℚ) : ℝ) ≤ stT277 246 := by
  have hc : ((301971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24066182787/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((301971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c247 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((48989/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125899/2500000) (δ := 6973/500000000) (ψ := -182979/200000) 277 243
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t247 : ((15584663083/250000000000 : ℚ) : ℝ) ≤ stT277 247 := by
  have hc : ((97973/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15584663083/250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((97973/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c248 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((123783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3301573/10000000) (δ := 6973/500000000) (ψ := -182979/200000) 277 243
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t248 : ((7858633/500000000 : ℚ) : ℝ) ≤ stT277 248 := by
  have hc : ((61879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7858633/500000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((61879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c249 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-95097/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3044131/5000000) (δ := 13857/1000000000) (ψ := -182979/200000) 277 243
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t249 : ((-9643089137/200000000000 : ℚ) : ℝ) ≤ stT277 249 := by
  have hc : ((-380413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9643089137/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-380413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c250 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-919513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1711023/2500000) (δ := 13853/1000000000) (ψ := -182979/200000) 277 244
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t250 : ((-72697892091/1250000000000 : ℚ) : ℝ) ≤ stT277 250 := by
  have hc : ((-919563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72697892091/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-919563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c251 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-61019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254977/625000) (δ := 13853/1000000000) (ψ := -182979/200000) 277 244
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t251 : ((-7709289491/2000000000000 : ℚ) : ℝ) ≤ stT277 251 := by
  have hc : ((-61069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7709289491/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-61069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c252 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((107821/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1326183/10000000) (δ := 279/20000000) (ψ := -182979/200000) 277 244
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t252 : ((13583364723/250000000000 : ℚ) : ℝ) ≤ stT277 252 := by
  have hc : ((431259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13583364723/250000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((431259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c253 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((421877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 708197/5000000) (δ := 279/20000000) (ψ := -182979/200000) 277 244
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t253 : ((33151977661/625000000000 : ℚ) : ℝ) ≤ stT277 253 := by
  have hc : ((105463/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33151977661/625000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((105463/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c254 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-22089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518521/1250000) (δ := 279/20000000) (ψ := -182979/200000) 277 244
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t254 : ((-108341553/19531250000 : ℚ) : ℝ) ≤ stT277 254 := by
  have hc : ((-44203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108341553/19531250000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-44203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c255 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-115427/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 858651/1250000) (δ := 281/20000000) (ψ := -182979/200000) 277 244
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t255 : ((-11565949917/200000000000 : ℚ) : ℝ) ≤ stT277 255 := by
  have hc : ((-461733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11565949917/200000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-461733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c256 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-771093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6128379/10000000) (δ := 693/50000000) (ψ := -182979/200000) 277 245
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t256 : ((-481965146143/10000000000000 : ℚ) : ℝ) ≤ stT277 256 := by
  have hc : ((-771143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-481965146143/10000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-771143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c257 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((198039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3428599/10000000) (δ := 14043/1000000000) (ψ := -182979/200000) 277 245
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t257 : ((61750987199/5000000000000 : ℚ) : ℝ) ≤ stT277 257 := by
  have hc : ((197989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61750987199/5000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((197989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c258 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((191319/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29571/400000) (δ := 13943/1000000000) (ψ := -182979/200000) 277 245
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t258 : ((29775906687/500000000000 : ℚ) : ℝ) ≤ stT277 258 := by
  have hc : ((191309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29775906687/500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((191309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c259 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((89227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1939661/10000000) (δ := 14043/1000000000) (ψ := -182979/200000) 277 245
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t259 : ((221756032827/5000000000000 : ℚ) : ℝ) ≤ stT277 259 := by
  have hc : ((356883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221756032827/5000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((356883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c260 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-53831/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4608279/10000000) (δ := 14043/1000000000) (ψ := -182979/200000) 277 245
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t260 : ((-16695394167/1000000000000 : ℚ) : ℝ) ≤ stT277 260 := by
  have hc : ((-53841/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16695394167/1000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-53841/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c261 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-97253/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 908331/1250000) (δ := 14043/1000000000) (ψ := -182979/200000) 277 245
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t261 : ((-6020124313/100000000000 : ℚ) : ℝ) ≤ stT277 261 := by
  have hc : ((-48629/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6020124313/100000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-48629/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c262 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-2122/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2896563/5000000) (δ := 8347/200000000) (ψ := -182979/200000) 277 246
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t262 : ((-41954383927/1000000000000 : ℚ) : ℝ) ≤ stT277 262 := by
  have hc : ((-67909/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41954383927/1000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-67909/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c263 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((151947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3155047/10000000) (δ := 2787/200000000) (ψ := -182979/200000) 277 246
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t263 : ((23419763793/1250000000000 : ℚ) : ℝ) ≤ stT277 263 := by
  have hc : ((75961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23419763793/1250000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((75961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c264 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((977869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26347/500000) (δ := 1299/31250000) (ψ := -182979/200000) 277 246
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t264 : ((601805548283/10000000000000 : ℚ) : ℝ) ≤ stT277 264 := by
  have hc : ((977819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601805548283/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((977819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c265 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((670081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418239/2000000) (δ := 873/62500000) (ψ := -182979/200000) 277 246
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t265 : ((82319338629/2000000000000 : ℚ) : ℝ) ≤ stT277 265 := by
  have hc : ((670031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82319338629/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((670031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c266 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-76027/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587437/1250000) (δ := 3467/250000000) (ψ := -182979/200000) 277 246
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t266 : ((-4662285903/250000000000 : ℚ) : ℝ) ≤ stT277 266 := by
  have hc : ((-152079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4662285903/250000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-152079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c267 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-975369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1824491/2500000) (δ := 873/62500000) (ψ := -182979/200000) 277 246
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t267 : ((-596947649229/10000000000000 : ℚ) : ℝ) ≤ stT277 267 := by
  have hc : ((-975419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596947649229/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-975419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c268 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-42953/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5821227/10000000) (δ := 1741/125000000) (ψ := -182979/200000) 277 247
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t268 : ((-6559915761/156250000000 : ℚ) : ℝ) ≤ stT277 268 := by
  have hc : ((-343649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6559915761/156250000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-343649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c269 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((5411/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20263/62500) (δ := 1741/125000000) (ψ := -182979/200000) 277 247
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t269 : ((32985311/2000000000 : ℚ) : ℝ) ≤ stT277 269 := by
  have hc : ((541/2000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32985311/2000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((541/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c270 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((482019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -672489/10000000) (δ := 559/40000000) (ψ := -182979/200000) 277 247
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t270 : ((7333297713/125000000000 : ℚ) : ℝ) ≤ stT277 270 := by
  have hc : ((240997/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7333297713/125000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((240997/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c271 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((9103/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 943807/5000000) (δ := 111/8000000) (ψ := -182979/200000) 277 247
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t271 : ((1382323077/31250000000 : ℚ) : ℝ) ≤ stT277 271 := by
  have hc : ((72819/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1382323077/31250000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((72819/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c272 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-203073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443823/1000000) (δ := 111/8000000) (ψ := -182979/200000) 277 247
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t272 : ((-6158079991/500000000000 : ℚ) : ℝ) ≤ stT277 272 := by
  have hc : ((-203123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6158079991/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-203123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c273 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-939443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6979497/10000000) (δ := 1741/125000000) (ψ := -182979/200000) 277 247
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t273 : ((-142151867351/2500000000000 : ℚ) : ℝ) ≤ stT277 273 := by
  have hc : ((-939493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142151867351/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-939493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c274 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-788131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6196409/10000000) (δ := 6941/500000000) (ψ := -182979/200000) 277 248
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t274 : ((-476158270263/10000000000000 : ℚ) : ℝ) ≤ stT277 274 := by
  have hc : ((-788181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-476158270263/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-788181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c275 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((101143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3673701/10000000) (δ := 13921/1000000000) (ψ := -182979/200000) 277 248
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t275 : ((30480651523/5000000000000 : ℚ) : ℝ) ≤ stT277 275 := by
  have hc : ((101093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30480651523/5000000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((101093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c276 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((447129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9063/78125) (δ := 6991/500000000) (ψ := -182979/200000) 277 248
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t276 : ((2102537997/39062500000 : ℚ) : ℝ) ≤ stT277 276 := by
  have hc : ((13972/15625 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2102537997/39062500000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((13972/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c277 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((429419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2689/20000) (δ := 14021/1000000000) (ψ := -182979/200000) 277 248
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t277 : ((128998760177/2500000000000 : ℚ) : ℝ) ≤ stT277 277 := by
  have hc : ((214697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128998760177/2500000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((214697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c278 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((4349/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3839993/10000000) (δ := 14021/1000000000) (ψ := -182979/200000) 277 248
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t278 : ((130230387/62500000000 : ℚ) : ℝ) ≤ stT277 278 := by
  have hc : ((17371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130230387/62500000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((17371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c279 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-32763/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1581621/2500000) (δ := 6941/500000000) (ψ := -182979/200000) 277 248
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t279 : ((-784636561/16000000000 : ℚ) : ℝ) ≤ stT277 279 := by
  have hc : ((-6553/8000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-784636561/16000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-6553/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c280 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-185727/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -862973/1250000) (δ := 7007/500000000) (ψ := -182979/200000) 277 249
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t280 : ((-22199843451/400000000000 : ℚ) : ℝ) ≤ stT277 280 := by
  have hc : ((-185737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22199843451/400000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-185737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c281 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-25227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4435021/10000000) (δ := 13889/1000000000) (ψ := -182979/200000) 277 249
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t281 : ((-1204231623/100000000000 : ℚ) : ℝ) ≤ stT277 281 := by
  have hc : ((-100933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1204231623/100000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-100933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c282 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((14077/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246873/1250000) (δ := 13889/1000000000) (ψ := -182979/200000) 277 249
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t282 : ((2095532829/50000000000 : ℚ) : ℝ) ≤ stT277 282 := by
  have hc : ((3519/5000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2095532829/50000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((3519/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c283 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((61369/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 476327/10000000) (δ := 7007/500000000) (ψ := -182979/200000) 277 249
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t283 : ((145912832013/2500000000000 : ℚ) : ℝ) ≤ stT277 283 := by
  have hc : ((490927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145912832013/2500000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((490927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c284 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((392341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729763/2500000) (δ := 13889/1000000000) (ψ := -182979/200000) 277 249
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t284 : ((23278155649/1000000000000 : ℚ) : ℝ) ≤ stT277 284 := by
  have hc : ((392291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23278155649/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((392291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c285 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-135003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33457/62500) (δ := 6957/500000000) (ψ := -182979/200000) 277 249
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t285 : ((-159952592819/5000000000000 : ℚ) : ℝ) ≤ stT277 285 := by
  have hc : ((-270031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159952592819/5000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-270031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c286 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-999547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 388937/500000) (δ := 13889/1000000000) (ψ := -182979/200000) 277 249
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t286 : ((-591074700861/10000000000000 : ℚ) : ℝ) ≤ stT277 286 := by
  have hc : ((-999597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-591074700861/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-999597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c287 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-296207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5512121/10000000) (δ := 3499/250000000) (ψ := -182979/200000) 277 250
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t287 : ((-10928776089/312500000000 : ℚ) : ℝ) ≤ stT277 287 := by
  have hc : ((-37029/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10928776089/312500000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-37029/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c288 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((80871/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -775867/2500000) (δ := 13907/1000000000) (ψ := -182979/200000) 277 250
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t288 : ((19058510167/1000000000000 : ℚ) : ℝ) ≤ stT277 288 := by
  have hc : ((161717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19058510167/1000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((161717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c289 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((960709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175781/2500000) (δ := 3499/250000000) (ψ := -182979/200000) 277 250
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t289 : ((113018649373/2000000000000 : ℚ) : ℝ) ≤ stT277 289 := by
  have hc : ((960659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113018649373/2000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((960659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c290 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((780337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 844489/5000000) (δ := 14007/1000000000) (ψ := -182979/200000) 277 250
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t290 : ((22910006607/500000000000 : ℚ) : ℝ) ≤ stT277 290 := by
  have hc : ((780287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22910006607/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((780287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c291 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-58279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4072771/10000000) (δ := 13907/1000000000) (ψ := -182979/200000) 277 250
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t291 : ((-34193101419/10000000000000 : ℚ) : ℝ) ≤ stT277 291 := by
  have hc : ((-58329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34193101419/10000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-58329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c292 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-2644/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3224231/5000000) (δ := 3499/250000000) (ψ := -182979/200000) 277 250
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t292 : ((-24758017639/500000000000 : ℚ) : ℝ) ≤ stT277 292 := by
  have hc : ((-84613/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24758017639/500000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-84613/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c293 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-463437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6891983/10000000) (δ := 13999/1000000000) (ψ := -182979/200000) 277 251
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t293 : ((-135378872317/2500000000000 : ℚ) : ℝ) ≤ stT277 293 := by
  have hc : ((-231731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135378872317/2500000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-231731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c294 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-59967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2266283/5000000) (δ := 13899/1000000000) (ψ := -182979/200000) 277 251
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t294 : ((-17490382077/1250000000000 : ℚ) : ℝ) ≤ stT277 294 := by
  have hc : ((-119959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17490382077/1250000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-119959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c295 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((160739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2181113/10000000) (δ := 13899/1000000000) (ψ := -182979/200000) 277 251
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t295 : ((93578504283/2500000000000 : ℚ) : ℝ) ≤ stT277 295 := by
  have hc : ((321453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93578504283/2500000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((321453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c296 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((997891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20297/1250000) (δ := 13999/1000000000) (ψ := -182979/200000) 277 251
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t296 : ((289991553579/5000000000000 : ℚ) : ℝ) ≤ stT277 296 := by
  have hc : ((997841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289991553579/5000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((997841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c297 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((108197/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2497971/10000000) (δ := 13899/1000000000) (ψ := -182979/200000) 277 251
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t297 : ((31388186123/1000000000000 : ℚ) : ℝ) ≤ stT277 297 := by
  have hc : ((108187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31388186123/1000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((108187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c298 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-17589/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4825671/10000000) (δ := 13999/1000000000) (ψ := -182979/200000) 277 251
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t298 : ((-4076196831/200000000000 : ℚ) : ℝ) ≤ stT277 298 := by
  have hc : ((-35183/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4076196831/200000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-35183/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c299 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-7681/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 446601/625000) (δ := 3501/250000000) (ψ := -182979/200000) 277 251
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t299 : ((-4442268841/80000000000 : ℚ) : ℝ) ≤ stT277 299 := by
  have hc : ((-38407/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4442268841/80000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-38407/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c300 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-400591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6250159/10000000) (δ := 14011/1000000000) (ψ := -182979/200000) 277 252
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t300 : ((-28912006027/625000000000 : ℚ) : ℝ) ≤ stT277 300 := by
  have hc : ((-50077/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28912006027/625000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-50077/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c301 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-7467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1972829/5000000) (δ := 3473/250000000) (ψ := -182979/200000) 277 252
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t301 : ((-4332731147/10000000000000 : ℚ) : ℝ) ≤ stT277 301 := by
  have hc : ((-7517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4332731147/10000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-7517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c302 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((790293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -824387/5000000) (δ := 3473/250000000) (ψ := -182979/200000) 277 252
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t302 : ((90946696141/2000000000000 : ℚ) : ℝ) ≤ stT277 302 := by
  have hc : ((790243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90946696141/2000000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((790243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c303 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((967361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 640493/10000000) (δ := 14011/1000000000) (ψ := -182979/200000) 277 252
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t303 : ((138926173131/2500000000000 : ℚ) : ℝ) ≤ stT277 303 := by
  have hc : ((967311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138926173131/2500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((967311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c304 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((391179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2922211/10000000) (δ := 13911/1000000000) (ψ := -182979/200000) 277 252
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t304 : ((224327735531/10000000000000 : ℚ) : ℝ) ≤ stT277 304 := by
  have hc : ((391129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224327735531/10000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((391129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c305 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-243109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5196381/10000000) (δ := 13911/1000000000) (ψ := -182979/200000) 277 252
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t305 : ((-69609142633/2500000000000 : ℚ) : ℝ) ≤ stT277 305 := by
  have hc : ((-121567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69609142633/2500000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-121567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c306 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-987809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 746321/1000000) (δ := 1749/125000000) (ψ := -182979/200000) 277 252
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t306 : ((-282360725829/5000000000000 : ℚ) : ℝ) ≤ stT277 306 := by
  have hc : ((-987859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282360725829/5000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-987859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c307 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-733437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2992701/5000000) (δ := 7009/500000000) (ψ := -182979/200000) 277 253
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t307 : ((-418623768997/10000000000000 : ℚ) : ℝ) ≤ stT277 307 := by
  have hc : ((-733487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418623768997/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-733487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c308 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((38681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233337/625000) (δ := 7009/500000000) (ψ := -182979/200000) 277 253
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t308 : ((43020051/9765625000 : ℚ) : ℝ) ≤ stT277 308 := by
  have hc : ((1208/15625 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43020051/9765625000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((1208/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c309 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((82789/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -744327/5000000) (δ := 2797/200000000) (ψ := -182979/200000) 277 253
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t309 : ((18396157/390625000 : ℚ) : ℝ) ≤ stT277 309 := by
  have hc : ((2587/3125 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18396157/390625000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((2587/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c310 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((955477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 374407/5000000) (δ := 6959/500000000) (ψ := -182979/200000) 277 253
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t310 : ((542645274347/10000000000000 : ℚ) : ℝ) ≤ stT277 310 := by
  have hc : ((955427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((542645274347/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((955427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c311 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((370119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2979149/10000000) (δ := 7009/500000000) (ψ := -182979/200000) 277 253
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t311 : ((209846516243/10000000000000 : ℚ) : ℝ) ≤ stT277 311 := by
  have hc : ((370069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209846516243/10000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((370069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c312 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-244127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1300553/2500000) (δ := 2777/200000000) (ψ := -182979/200000) 277 253
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t312 : ((-17277996141/625000000000 : ℚ) : ℝ) ≤ stT277 312 := by
  have hc : ((-30519/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17277996141/625000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-30519/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c313 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-984847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1854553/2500000) (δ := 2777/200000000) (ψ := -182979/200000) 277 253
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t313 : ((-278348635449/5000000000000 : ℚ) : ℝ) ≤ stT277 313 := by
  have hc : ((-984897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278348635449/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-984897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c314 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-18971/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1216163/2000000) (δ := 6989/500000000) (ψ := -182979/200000) 277 254
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t314 : ((-42826667037/1000000000000 : ℚ) : ℝ) ≤ stT277 314 := by
  have hc : ((-75889/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42826667037/1000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-75889/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c315 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((9623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -484859/1250000) (δ := 561/40000000) (ψ := -182979/200000) 277 254
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t315 : ((675982341/625000000000 : ℚ) : ℝ) ≤ stT277 315 := by
  have hc : ((4799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((675982341/625000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((4799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c316 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((977/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -420981/2500000) (δ := 561/40000000) (ψ := -182979/200000) 277 254
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t316 : ((8793109633/200000000000 : ℚ) : ℝ) ≤ stT277 316 := by
  have hc : ((15631/20000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8793109633/200000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((15631/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c317 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((195949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504029/10000000) (δ := 6989/500000000) (ψ := -182979/200000) 277 254
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t317 : ((22010023809/400000000000 : ℚ) : ℝ) ≤ stT277 317 := by
  have hc : ((195939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22010023809/400000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((195939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c318 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((476567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2685127/10000000) (δ := 6989/500000000) (ψ := -182979/200000) 277 254
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t318 : ((66804347781/2500000000000 : ℚ) : ℝ) ≤ stT277 318 := by
  have hc : ((476517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66804347781/2500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((476517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c319 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-364391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4859439/10000000) (δ := 557/40000000) (ψ := -182979/200000) 277 254
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t319 : ((-204047964813/10000000000000 : ℚ) : ℝ) ≤ stT277 319 := by
  have hc : ((-364441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204047964813/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-364441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c320 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-472881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281073/400000) (δ := 6989/500000000) (ψ := -182979/200000) 277 254
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t320 : ((-132181246701/2500000000000 : ℚ) : ℝ) ≤ stT277 320 := by
  have hc : ((-236453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132181246701/2500000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-236453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c321 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-430533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6520399/10000000) (δ := 877/62500000) (ψ := -182979/200000) 277 255
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t321 : ((-60078556367/1250000000000 : ℚ) : ℝ) ≤ stT277 321 := by
  have hc : ((-215279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60078556367/1250000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-215279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c322 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-174879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4366447/10000000) (δ := 877/62500000) (ψ := -182979/200000) 277 255
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t322 : ((-97484258191/10000000000000 : ℚ) : ℝ) ≤ stT277 322 := by
  have hc : ((-174929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97484258191/10000000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-174929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c323 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((631231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2219143/10000000) (δ := 877/62500000) (ψ := -182979/200000) 277 255
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t323 : ((175598972467/5000000000000 : ℚ) : ℝ) ≤ stT277 323 := by
  have hc : ((631181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175598972467/5000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((631181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c324 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((999507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78487/10000000) (δ := 877/62500000) (ψ := -182979/200000) 277 255
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t324 : ((111050666727/2000000000000 : ℚ) : ℝ) ≤ stT277 324 := by
  have hc : ((999457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111050666727/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((999457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c325 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((136121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2055521/10000000) (δ := 877/62500000) (ψ := -182979/200000) 277 255
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t325 : ((755007717/20000000000 : ℚ) : ℝ) ≤ stT277 325 := by
  have hc : ((136111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((755007717/20000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((136111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c326 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-12779/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4183019/10000000) (δ := 13871/1000000000) (ψ := -182979/200000) 277 255
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t326 : ((-28324391709/5000000000000 : ℚ) : ℝ) ≤ stT277 326 := by
  have hc : ((-51141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28324391709/5000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-51141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c327 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-162777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 788001/1250000) (δ := 13871/1000000000) (ψ := -182979/200000) 277 255
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t327 : ((-45010768287/1000000000000 : ℚ) : ℝ) ≤ stT277 327 := by
  have hc : ((-162787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45010768287/1000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-162787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c328 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-974609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3644703/5000000) (δ := 14039/1000000000) (ψ := -182979/200000) 277 256
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t328 : ((-269082882061/5000000000000 : ℚ) : ℝ) ≤ stT277 328 := by
  have hc : ((-974659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269082882061/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-974659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c329 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-480961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5181367/10000000) (δ := 13939/1000000000) (ψ := -182979/200000) 277 256
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t329 : ((-132595011249/5000000000000 : ℚ) : ℝ) ≤ stT277 329 := by
  have hc : ((-481011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132595011249/5000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-481011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c330 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((166233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3079699/10000000) (δ := 1733/125000000) (ψ := -182979/200000) 277 256
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t330 : ((1429599157/78125000000 : ℚ) : ℝ) ≤ stT277 330 := by
  have hc : ((5194/15625 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1429599157/78125000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((5194/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c331 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((923473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -492201/5000000) (δ := 3491/250000000) (ψ := -182979/200000) 277 256
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t331 : ((507558528527/10000000000000 : ℚ) : ℝ) ≤ stT277 331 := by
  have hc : ((923423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507558528527/10000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((923423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c332 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((903967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 552297/5000000) (δ := 13939/1000000000) (ψ := -182979/200000) 277 256
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t332 : ((496088631857/10000000000000 : ℚ) : ℝ) ≤ stT277 332 := by
  have hc : ((903917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496088631857/10000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((903917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c333 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((291583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398411/1250000) (δ := 14039/1000000000) (ψ := -182979/200000) 277 256
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t333 : ((39939729467/2500000000000 : ℚ) : ℝ) ≤ stT277 333 := by
  have hc : ((291533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39939729467/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((291533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c334 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-254793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5263749/10000000) (δ := 13939/1000000000) (ψ := -182979/200000) 277 256
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t334 : ((-8714393373/312500000000 : ℚ) : ℝ) ≤ stT277 334 := by
  have hc : ((-127409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8714393373/312500000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-127409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c335 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-978451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7334047/10000000) (δ := 13939/1000000000) (ψ := -182979/200000) 277 256
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t335 : ((-534612827859/10000000000000 : ℚ) : ℝ) ≤ stT277 335 := by
  have hc : ((-978501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534612827859/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-978501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c336 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-20381/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6309851/10000000) (δ := 433/31250000) (ψ := -182979/200000) 277 257
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t336 : ((-8895547661/200000000000 : ℚ) : ℝ) ≤ stT277 336 := by
  have hc : ((-81529/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8895547661/200000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-81529/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c337 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-12959/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4251879/10000000) (δ := 14047/1000000000) (ψ := -182979/200000) 277 257
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t337 : ((-353097227/50000000000 : ℚ) : ℝ) ≤ stT277 337 := by
  have hc : ((-3241/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353097227/50000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-3241/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c338 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((637129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2200071/10000000) (δ := 13947/1000000000) (ψ := -182979/200000) 277 257
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t338 : ((43315638289/1250000000000 : ℚ) : ℝ) ≤ stT277 338 := by
  have hc : ((637079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43315638289/1250000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((637079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c339 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((499049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77109/5000000) (δ := 14047/1000000000) (ψ := -182979/200000) 277 257
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t339 : ((27103241/500000000 : ℚ) : ℝ) ≤ stT277 339 := by
  have hc : ((31189/31250 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27103241/500000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((31189/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c340 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((728809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94277/500000) (δ := 3489/250000000) (ψ := -182979/200000) 277 257
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t340 : ((197612476717/5000000000000 : ℚ) : ℝ) ≤ stT277 340 := by
  have hc : ((728759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197612476717/5000000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((728759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c341 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((3087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1959637/5000000) (δ := 3489/250000000) (ψ := -182979/200000) 277 257
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t341 : ((164462661/1000000000000 : ℚ) : ℝ) ≤ stT277 341 := by
  have hc : ((3037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164462661/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((3037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c342 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-722943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2973561/5000000) (δ := 433/31250000) (ψ := -182979/200000) 277 257
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t342 : ((-390950511827/10000000000000 : ℚ) : ℝ) ≤ stT277 342 := by
  have hc : ((-722993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390950511827/10000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-722993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c343 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-499471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7738949/10000000) (δ := 6927/500000000) (ψ := -182979/200000) 277 258
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t343 : ((-674257163/12500000000 : ℚ) : ℝ) ≤ stT277 343 := by
  have hc : ((-62437/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-674257163/12500000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-62437/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c344 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-658167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5722943/10000000) (δ := 6927/500000000) (ψ := -182979/200000) 277 258
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t344 : ((-88721727647/2500000000000 : ℚ) : ℝ) ≤ stT277 344 := by
  have hc : ((-658217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88721727647/2500000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-658217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c345 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((8559/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1856377/5000000) (δ := 6927/500000000) (ψ := -182979/200000) 277 258
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t345 : ((2302655537/500000000000 : ℚ) : ℝ) ≤ stT277 345 := by
  have hc : ((4277/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2302655537/500000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((4277/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c346 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((775443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1708451/10000000) (δ := 6977/500000000) (ψ := -182979/200000) 277 258
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t346 : ((416853602979/10000000000000 : ℚ) : ℝ) ≤ stT277 346 := by
  have hc : ((775393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416853602979/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((775393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c347 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((39731/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36263/1250000) (δ := 6977/500000000) (ψ := -182979/200000) 277 258
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t347 : ((5331909903/100000000000 : ℚ) : ℝ) ≤ stT277 347 := by
  have hc : ((39729/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5331909903/100000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((39729/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c348 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((152811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2282911/10000000) (δ := 6927/500000000) (ψ := -182979/200000) 277 258
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t348 : ((20477138179/625000000000 : ℚ) : ℝ) ≤ stT277 348 := by
  have hc : ((305597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20477138179/625000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((305597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c349 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-136789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 106751/250000) (δ := 6977/500000000) (ψ := -182979/200000) 277 258
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t349 : ((-9156034329/1250000000000 : ℚ) : ℝ) ≤ stT277 349 := by
  have hc : ((-136839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9156034329/1250000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-136839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c350 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-200371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6251421/10000000) (δ := 6977/500000000) (ψ := -182979/200000) 277 258
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t350 : ((-214219179141/5000000000000 : ℚ) : ℝ) ≤ stT277 350 := by
  have hc : ((-400767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214219179141/5000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-400767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c351 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-494439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7480771/10000000) (δ := 6971/500000000) (ψ := -182979/200000) 277 259
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t351 : ((-2061918743/39062500000 : ℚ) : ℝ) ≤ stT277 351 := by
  have hc : ((-15452/15625 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2061918743/39062500000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-15452/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c352 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-591949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2755339/5000000) (δ := 7021/500000000) (ψ := -182979/200000) 277 259
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t352 : ((-157768325499/5000000000000 : ℚ) : ℝ) ≤ stT277 352 := by
  have hc : ((-591999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157768325499/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-591999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c353 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((75879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -886531/2500000) (δ := 13961/1000000000) (ψ := -182979/200000) 277 259
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t353 : ((10093247021/1250000000000 : ℚ) : ℝ) ≤ stT277 353 := by
  have hc : ((37927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10093247021/1250000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((37927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c354 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((201291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1587111/10000000) (δ := 13861/1000000000) (ψ := -182979/200000) 277 259
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t354 : ((106978315079/2500000000000 : ℚ) : ℝ) ≤ stT277 354 := by
  have hc : ((402557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106978315079/2500000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((402557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c355 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((494643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 366293/10000000) (δ := 13861/1000000000) (ψ := -182979/200000) 277 259
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t355 : ((16407220987/312500000000 : ℚ) : ℝ) ≤ stT277 355 := by
  have hc : ((247309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16407220987/312500000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((247309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c356 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((601261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462859/2000000) (δ := 7021/500000000) (ψ := -182979/200000) 277 259
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t356 : ((159320313789/5000000000000 : ℚ) : ℝ) ≤ stT277 356 := by
  have hc : ((601211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159320313789/5000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((601211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c357 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-5261/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2128379/5000000) (δ := 13861/1000000000) (ψ := -182979/200000) 277 259
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t357 : ((-2785479591/400000000000 : ℚ) : ℝ) ≤ stT277 357 := by
  have hc : ((-5263/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2785479591/400000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-5263/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c358 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-787493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6193819/10000000) (δ := 13861/1000000000) (ψ := -182979/200000) 277 259
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t358 : ((-416229863731/10000000000000 : ℚ) : ℝ) ≤ stT277 358 := by
  have hc : ((-787543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416229863731/10000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-787543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c359 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-994109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1516497/2000000) (δ := 2787/200000000) (ψ := -182979/200000) 277 260
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t359 : ((-26234861851/500000000000 : ℚ) : ℝ) ≤ stT277 359 := by
  have hc : ((-994159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26234861851/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-994159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c360 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-318911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2828079/5000000) (δ := 2807/200000000) (ψ := -182979/200000) 277 260
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t360 : ((-21011782749/625000000000 : ℚ) : ℝ) ≤ stT277 360 := by
  have hc : ((-39867/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21011782749/625000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-39867/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c361 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((19157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58363/156250) (δ := 2787/200000000) (ψ := -182979/200000) 277 260
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t361 : ((4030415007/1000000000000 : ℚ) : ℝ) ≤ stT277 361 := by
  have hc : ((38289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4030415007/1000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((38289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c362 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((746621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1819569/10000000) (δ := 3467/250000000) (ψ := -182979/200000) 277 260
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t362 : ((98097189687/2500000000000 : ℚ) : ℝ) ≤ stT277 362 := by
  have hc : ((746571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98097189687/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((746571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c363 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((999341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90761/10000000) (δ := 2807/200000000) (ψ := -182979/200000) 277 260
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t363 : ((524490872133/10000000000000 : ℚ) : ℝ) ≤ stT277 363 := by
  have hc : ((999291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((524490872133/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((999291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c364 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((697903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1995829/10000000) (δ := 3467/250000000) (ψ := -182979/200000) 277 260
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t364 : ((182887033563/5000000000000 : ℚ) : ℝ) ≤ stT277 364 := by
  have hc : ((697853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182887033563/5000000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((697853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c365 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((2503/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3895703/10000000) (δ := 873/62500000) (ψ := -182979/200000) 277 260
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t365 : ((1304893539/2000000000000 : ℚ) : ℝ) ≤ stT277 365 := by
  have hc : ((2493/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1304893539/2000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((2493/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c366 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-339117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5790383/10000000) (δ := 873/62500000) (ψ := -182979/200000) 277 260
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t366 : ((-88636287839/2500000000000 : ℚ) : ℝ) ≤ stT277 366 := by
  have hc : ((-169571/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88636287839/2500000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-169571/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c367 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-124697/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7679869/10000000) (δ := 3467/250000000) (ψ := -182979/200000) 277 260
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t367 : ((-65094597687/1250000000000 : ℚ) : ℝ) ≤ stT277 367 := by
  have hc : ((-498813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65094597687/1250000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-498813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c368 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-193747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6143733/10000000) (δ := 3507/250000000) (ψ := -182979/200000) 277 261
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t368 : ((-202008616953/5000000000000 : ℚ) : ℝ) ≤ stT277 368 := by
  have hc : ((-387519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202008616953/5000000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-387519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c369 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-2103/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -852899/2000000) (δ := 559/40000000) (ψ := -182979/200000) 277 261
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t369 : ((-1752298309/250000000000 : ℚ) : ℝ) ≤ stT277 369 := by
  have hc : ((-67321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1752298309/250000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-67321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c370 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((57669/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2390313/10000000) (δ := 559/40000000) (ψ := -182979/200000) 277 261
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t370 : ((3747259/125000000 : ℚ) : ℝ) ≤ stT277 370 := by
  have hc : ((1802/3125 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3747259/125000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((1802/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c371 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((489171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65157/1250000) (δ := 1741/125000000) (ψ := -182979/200000) 277 261
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t371 : ((63487971351/1250000000000 : ℚ) : ℝ) ≤ stT277 371 := by
  have hc : ((244573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63487971351/1250000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((244573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c372 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((859183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41963/312500) (δ := 559/40000000) (ψ := -182979/200000) 277 261
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t372 : ((17817559287/400000000000 : ℚ) : ℝ) ≤ stT277 372 := by
  have hc : ((859133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17817559287/400000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((859133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c373 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((285987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3201901/10000000) (δ := 1741/125000000) (ψ := -182979/200000) 277 261
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t373 : ((7402622993/500000000000 : ℚ) : ℝ) ≤ stT277 373 := by
  have hc : ((285937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7402622993/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((285937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c374 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-13637/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5055931/10000000) (δ := 3507/250000000) (ψ := -182979/200000) 277 261
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t374 : ((-3526168503/156250000000 : ℚ) : ℝ) ≤ stT277 374 := by
  have hc : ((-218217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3526168503/156250000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-218217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c375 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-928833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3452557/5000000) (δ := 1741/125000000) (ψ := -182979/200000) 277 261
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t375 : ((-239836661717/5000000000000 : ℚ) : ℝ) ≤ stT277 375 := by
  have hc : ((-928883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239836661717/5000000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-928883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c376 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-936553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1739663/2500000) (δ := 13983/1000000000) (ψ := -182979/200000) 277 262
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t376 : ((-483016469733/10000000000000 : ℚ) : ℝ) ≤ stT277 376 := by
  have hc : ((-936603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483016469733/10000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-936603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c377 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-229537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1279843/2500000) (δ := 13983/1000000000) (ψ := -182979/200000) 277 262
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t377 : ((-59115314087/2500000000000 : ℚ) : ℝ) ≤ stT277 377 := by
  have hc : ((-114781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59115314087/2500000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-114781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c378 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((127003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164247/500000) (δ := 87/6250000) (ψ := -182979/200000) 277 262
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t378 : ((4081898277/312500000000 : ℚ) : ℝ) ≤ stT277 378 := by
  have hc : ((63489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4081898277/312500000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((63489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c379 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((417651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727643/5000000) (δ := 701/50000000) (ψ := -182979/200000) 277 262
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t379 : ((21451985929/500000000000 : ℚ) : ℝ) ≤ stT277 379 := by
  have hc : ((208813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21451985929/500000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((208813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c380 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((9891/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92363/2500000) (δ := 13883/1000000000) (ψ := -182979/200000) 277 262
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t380 : ((10147435409/200000000000 : ℚ) : ℝ) ≤ stT277 380 := by
  have hc : ((19781/20000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10147435409/200000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((19781/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c381 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((64041/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2189411/10000000) (δ := 87/6250000) (ψ := -182979/200000) 277 262
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t381 : ((1640330167/50000000000 : ℚ) : ℝ) ≤ stT277 381 := by
  have hc : ((16009/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1640330167/50000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((16009/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c382 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-31063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4004661/10000000) (δ := 701/50000000) (ψ := -182979/200000) 277 262
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t382 : ((-3183762177/2000000000000 : ℚ) : ℝ) ≤ stT277 382 := by
  have hc : ((-31113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3183762177/2000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-31113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c383 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-42841/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 726883/1250000) (δ := 87/6250000) (ψ := -182979/200000) 277 262
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t383 : ((-175138899681/5000000000000 : ℚ) : ℝ) ≤ stT277 383 := by
  have hc : ((-342753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175138899681/5000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-342753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c384 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-497827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7620827/10000000) (δ := 87/6250000) (ψ := -182979/200000) 277 262
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t384 : ((-63514837993/1250000000000 : ℚ) : ℝ) ≤ stT277 384 := by
  have hc : ((-124463/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63514837993/1250000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-124463/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c385 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-404849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3143041/5000000) (δ := 1389/100000000) (ψ := -182979/200000) 277 263
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t385 : ((-6448225761/156250000000 : ℚ) : ℝ) ≤ stT277 385 := by
  have hc : ((-202437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6448225761/156250000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-202437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c386 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-111601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4489737/10000000) (δ := 1389/100000000) (ψ := -182979/200000) 277 263
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t386 : ((-28408091431/2500000000000 : ℚ) : ℝ) ≤ stT277 386 := by
  have hc : ((-55813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28408091431/2500000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-55813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c387 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((236011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168627/625000) (δ := 13913/1000000000) (ψ := -182979/200000) 277 263
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t387 : ((7497393213/312500000000 : ℚ) : ℝ) ≤ stT277 387 := by
  have hc : ((117993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7497393213/312500000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((117993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c388 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((58397/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -910897/10000000) (δ := 1389/100000000) (ψ := -182979/200000) 277 263
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t388 : ((237159949623/5000000000000 : ℚ) : ℝ) ≤ stT277 388 := by
  have hc : ((467151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237159949623/5000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((467151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c389 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((469919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 435799/5000000) (δ := 1389/100000000) (ψ := -182979/200000) 277 263
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t389 : ((5956141397/125000000000 : ℚ) : ℝ) ≤ stT277 389 := by
  have hc : ((234947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5956141397/125000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((234947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c390 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((489039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1324761/5000000) (δ := 14013/1000000000) (ψ := -182979/200000) 277 263
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t390 : ((247608870941/10000000000000 : ℚ) : ℝ) ≤ stT277 390 := by
  have hc : ((488989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247608870941/10000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((488989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c391 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-3079/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1105719/2500000) (δ := 14013/1000000000) (ψ := -182979/200000) 277 263
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t391 : ((-24920210133/2500000000000 : ℚ) : ℝ) ≤ stT277 391 := by
  have hc : ((-98553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24920210133/2500000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-98553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c392 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-393489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6191729/10000000) (δ := 13913/1000000000) (ψ := -182979/200000) 277 263
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t392 : ((-99377435289/2500000000000 : ℚ) : ℝ) ≤ stT277 392 := by
  have hc : ((-196757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99377435289/2500000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-196757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c393 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-499583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7751883/10000000) (δ := 7003/500000000) (ψ := -182979/200000) 277 264
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t393 : ((-15751203867/312500000000 : ℚ) : ℝ) ≤ stT277 393 := by
  have hc : ((-62451/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15751203867/312500000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-62451/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c394 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-735237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187251/312500) (δ := 13997/1000000000) (ψ := -182979/200000) 277 264
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t394 : ((-370432443591/10000000000000 : ℚ) : ℝ) ≤ stT277 394 := by
  have hc : ((-735287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370432443591/10000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-735287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c395 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-3089/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4236683/10000000) (δ := 13997/1000000000) (ψ := -182979/200000) 277 264
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t395 : ((-1243899791/200000000000 : ℚ) : ℝ) ≤ stT277 395 := by
  have hc : ((-12361/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1243899791/200000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-12361/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c396 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((136277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2485697/10000000) (δ := 13897/1000000000) (ψ := -182979/200000) 277 264
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t396 : ((68475364011/2500000000000 : ℚ) : ℝ) ≤ stT277 396 := by
  have hc : ((272529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68475364011/2500000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((272529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c397 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((956603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184803/2500000) (δ := 13897/1000000000) (ψ := -182979/200000) 277 264
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t397 : ((96015920481/2000000000000 : ℚ) : ℝ) ≤ stT277 397 := by
  have hc : ((956553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96015920481/2000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((956553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c398 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((230149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1002979/10000000) (δ := 7003/500000000) (ψ := -182979/200000) 277 264
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t398 : ((115356841171/2500000000000 : ℚ) : ℝ) ≤ stT277 398 := by
  have hc : ((460273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115356841171/2500000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((460273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c399 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((228447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2740739/10000000) (δ := 13897/1000000000) (ψ := -182979/200000) 277 264
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t399 : ((28588498043/1250000000000 : ℚ) : ℝ) ≤ stT277 399 := by
  have hc : ((114211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28588498043/1250000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((114211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c400 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-43423/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559267/1250000) (δ := 13997/1000000000) (ψ := -182979/200000) 277 264
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t400 : ((-21716543433/2000000000000 : ℚ) : ℝ) ≤ stT277 400 := by
  have hc : ((-43433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21716543433/2000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-43433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c401 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-78981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6203239/10000000) (δ := 13897/1000000000) (ψ := -182979/200000) 277 264
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t401 : ((-19721895861/500000000000 : ℚ) : ℝ) ≤ stT277 401 := by
  have hc : ((-39493/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19721895861/500000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-39493/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c402 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-499781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486249/625000) (δ := 13899/1000000000) (ψ := -182979/200000) 277 265
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t402 : ((-24928074153/500000000000 : ℚ) : ℝ) ≤ stT277 402 := by
  have hc : ((-249903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24928074153/500000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-249903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c403 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-753251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1514867/2500000) (δ := 13999/1000000000) (ψ := -182979/200000) 277 265
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t403 : ((-46905793367/1250000000000 : ℚ) : ℝ) ≤ stT277 403 := by
  have hc : ((-753301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46905793367/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-753301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c404 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-165733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -868649/2000000) (δ := 13899/1000000000) (ψ := -182979/200000) 277 265
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t404 : ((-82480192377/10000000000000 : ℚ) : ℝ) ≤ stT277 404 := by
  have hc : ((-165783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82480192377/10000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-165783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c405 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((247701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1315623/5000000) (δ := 3501/250000000) (ψ := -182979/200000) 277 265
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t405 : ((30767736857/1250000000000 : ℚ) : ℝ) ≤ stT277 405 := by
  have hc : ((61919/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30767736857/1250000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((61919/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c406 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((233137/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57717/625000) (δ := 869/62500000) (ψ := -182979/200000) 277 265
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t406 : ((231395182459/5000000000000 : ℚ) : ℝ) ≤ stT277 406 := by
  have hc : ((466249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231395182459/5000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((466249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c407 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((29741/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 390039/5000000) (δ := 869/62500000) (ψ := -182979/200000) 277 265
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t407 : ((235860385911/5000000000000 : ℚ) : ℝ) ≤ stT277 407 := by
  have hc : ((475831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235860385911/5000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((475831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c408 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((547193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2479473/10000000) (δ := 869/62500000) (ψ := -182979/200000) 277 265
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t408 : ((270875726439/10000000000000 : ℚ) : ℝ) ≤ stT277 408 := by
  have hc : ((547143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270875726439/10000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((547143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c409 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-98927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4174713/10000000) (δ := 869/62500000) (ψ := -182979/200000) 277 265
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t409 : ((-48941058213/10000000000000 : ℚ) : ℝ) ≤ stT277 409 := by
  have hc : ((-98977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48941058213/10000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-98977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c410 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-70009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2932899/5000000) (δ := 869/62500000) (ψ := -182979/200000) 277 265
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t410 : ((-3457746411/100000000000 : ℚ) : ℝ) ≤ stT277 410 := by
  have hc : ((-35007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3457746411/100000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-35007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c411 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-62047/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7552797/10000000) (δ := 13899/1000000000) (ψ := -182979/200000) 277 265
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t411 : ((-15303546429/312500000000 : ℚ) : ℝ) ≤ stT277 411 := by
  have hc : ((-496401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15303546429/312500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-496401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c412 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-851129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3236161/5000000) (δ := 3473/250000000) (ψ := -182979/200000) 277 266
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t412 : ((-83869220407/2000000000000 : ℚ) : ℝ) ≤ stT277 412 := by
  have hc : ((-851179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83869220407/2000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-851179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c413 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-339729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4793563/10000000) (δ := 14011/1000000000) (ψ := -182979/200000) 277 266
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t413 : ((-41798593243/2500000000000 : ℚ) : ℝ) ≤ stT277 413 := by
  have hc : ((-339779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41798593243/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-339779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c414 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((317667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3118821/10000000) (δ := 14011/1000000000) (ψ := -182979/200000) 277 266
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t414 : ((156100179841/10000000000000 : ℚ) : ℝ) ≤ stT277 414 := by
  have hc : ((317617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156100179841/10000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((317617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c415 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((10461/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45253/312500) (δ := 3473/250000000) (ψ := -182979/200000) 277 266
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t415 : ((64184861/1562500000 : ℚ) : ℝ) ≤ stT277 415 := by
  have hc : ((83683/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64184861/1562500000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((83683/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c416 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((498091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13659/625000) (δ := 13911/1000000000) (ψ := -182979/200000) 277 266
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t416 : ((12209838957/250000000000 : ℚ) : ℝ) ≤ stT277 416 := by
  have hc : ((249033/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12209838957/250000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((249033/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c417 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((364993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 470309/2500000) (δ := 1749/125000000) (ψ := -182979/200000) 277 266
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t417 : ((11170347471/312500000000 : ℚ) : ℝ) ≤ stT277 417 := by
  have hc : ((45621/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11170347471/312500000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((45621/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c418 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((77107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 442489/1250000) (δ := 1749/125000000) (ψ := -182979/200000) 277 266
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t418 : ((3770196243/500000000000 : ℚ) : ℝ) ≤ stT277 418 := by
  have hc : ((38541/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3770196243/500000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((38541/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c419 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-485609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5194641/10000000) (δ := 3473/250000000) (ψ := -182979/200000) 277 266
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t419 : ((-59314990647/2500000000000 : ℚ) : ℝ) ≤ stT277 419 := by
  have hc : ((-485659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59314990647/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-485659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c420 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-459861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6845423/10000000) (δ := 14011/1000000000) (ψ := -182979/200000) 277 266
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t420 : ((-112200916793/2500000000000 : ℚ) : ℝ) ≤ stT277 420 := by
  have hc : ((-229943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112200916793/2500000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-229943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c421 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-193517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3607853/5000000) (δ := 7009/500000000) (ψ := -182979/200000) 277 267
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t421 : ((-94319447517/2000000000000 : ℚ) : ℝ) ≤ stT277 421 := by
  have hc : ((-193527/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94319447517/2000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-193527/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c422 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-9559/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22291/40000) (δ := 6959/500000000) (ψ := -182979/200000) 277 267
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t422 : ((-148916307009/5000000000000 : ℚ) : ℝ) ≤ stT277 422 := by
  have hc : ((-305913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148916307009/5000000000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-305913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c423 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-27/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3933741/10000000) (δ := 6959/500000000) (ψ := -182979/200000) 277 267
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t423 : ((-5348387/40000000000 : ℚ) : ℝ) ≤ stT277 423 := by
  have hc : ((-11/4000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5348387/40000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-11/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c424 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((151571/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2298541/10000000) (δ := 2777/200000000) (ψ := -182979/200000) 277 267
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t424 : ((73603173057/2500000000000 : ℚ) : ℝ) ≤ stT277 424 := by
  have hc : ((303117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73603173057/2500000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((303117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c425 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((241149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -667219/10000000) (δ := 2797/200000000) (ψ := -182979/200000) 277 267
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t425 : ((233936646383/5000000000000 : ℚ) : ℝ) ≤ stT277 425 := by
  have hc : ((482273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233936646383/5000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((482273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c426 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((927129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192059/2000000) (δ := 6959/500000000) (ψ := -182979/200000) 277 267
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t426 : ((449170702579/10000000000000 : ℚ) : ℝ) ≤ stT277 426 := by
  have hc : ((927079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449170702579/10000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((927079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c427 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((511729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323/1250) (δ := 7009/500000000) (ψ := -182979/200000) 277 267
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t427 : ((247618353507/10000000000000 : ℚ) : ℝ) ≤ stT277 427 := by
  have hc : ((511679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247618353507/10000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((511679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c428 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-27627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2101913/5000000) (δ := 2797/200000000) (ψ := -182979/200000) 277 267
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t428 : ((-26720154951/5000000000000 : ℚ) : ℝ) ≤ stT277 428 := by
  have hc : ((-55279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26720154951/5000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-55279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c429 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-686887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5819983/10000000) (δ := 6959/500000000) (ψ := -182979/200000) 277 267
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t429 : ((-66331323657/2000000000000 : ℚ) : ℝ) ≤ stT277 429 := by
  have hc : ((-686937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66331323657/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-686937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c430 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-985811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7432331/10000000) (δ := 7009/500000000) (ψ := -182979/200000) 277 267
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t430 : ((-475424566223/10000000000000 : ℚ) : ℝ) ≤ stT277 430 := by
  have hc : ((-985861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475424566223/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-985861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c431 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-177881/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3333547/5000000) (δ := 13977/1000000000) (ψ := -182979/200000) 277 268
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t431 : ((-21421812111/500000000000 : ℚ) : ℝ) ≤ stT277 431 := by
  have hc : ((-177891/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21421812111/500000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-177891/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c432 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-54831/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -202489/400000) (δ := 13877/1000000000) (ψ := -182979/200000) 277 268
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t432 : ((-52767253487/2500000000000 : ℚ) : ℝ) ≤ stT277 432 := by
  have hc : ((-219349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52767253487/2500000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-219349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c433 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((185309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1730513/5000000) (δ := 7013/500000000) (ψ := -182979/200000) 277 268
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t433 : ((89029732371/10000000000000 : ℚ) : ℝ) ≤ stT277 433 := by
  have hc : ((185259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89029732371/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((185259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c434 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((367399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1863567/10000000) (δ := 7013/500000000) (ψ := -182979/200000) 277 268
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t434 : ((17634503061/500000000000 : ℚ) : ℝ) ≤ stT277 434 := by
  have hc : ((183687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17634503061/500000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((183687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c435 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((994183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269779/10000000) (δ := 13977/1000000000) (ψ := -182979/200000) 277 268
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t435 : ((476649990579/10000000000000 : ℚ) : ℝ) ≤ stT277 435 := by
  have hc : ((994133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476649990579/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((994133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c436 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((215937/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66017/500000) (δ := 6963/500000000) (ψ := -182979/200000) 277 268
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t436 : ((206818100137/5000000000000 : ℚ) : ℝ) ≤ stT277 436 := by
  have hc : ((431849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206818100137/5000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((431849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c437 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((396849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 726697/2500000) (δ := 13877/1000000000) (ψ := -182979/200000) 277 268
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t437 : ((47453589209/2500000000000 : ℚ) : ℝ) ≤ stT277 437 := by
  have hc : ((396799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47453589209/2500000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((396799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c438 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-22319/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897941/2000000) (δ := 7013/500000000) (ψ := -182979/200000) 277 268
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t438 : ((-2666707839/250000000000 : ℚ) : ℝ) ≤ stT277 438 := by
  have hc : ((-5581/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2666707839/250000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-5581/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c439 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-37787/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6068951/10000000) (δ := 6963/500000000) (ψ := -182979/200000) 277 268
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t439 : ((-18035945823/500000000000 : ℚ) : ℝ) ≤ stT277 439 := by
  have hc : ((-75579/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18035945823/500000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-75579/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c440 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-199299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1911149/2500000) (δ := 13877/1000000000) (ψ := -182979/200000) 277 268
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t440 : ((-23754244547/500000000000 : ℚ) : ℝ) ≤ stT277 440 := by
  have hc : ((-199309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23754244547/500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-199309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c441 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-427547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6491323/10000000) (δ := 1387/100000000) (ψ := -182979/200000) 277 269
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t441 : ((-50901484563/1250000000000 : ℚ) : ℝ) ≤ stT277 441 := by
  have hc : ((-106893/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50901484563/1250000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-106893/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c442 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-387877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -492281/1000000) (δ := 14033/1000000000) (ψ := -182979/200000) 277 269
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t442 : ((-46129563351/2500000000000 : ℚ) : ℝ) ≤ stT277 442 := by
  have hc : ((-387927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46129563351/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-387927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c443 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((225703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335783/1000000) (δ := 1397/100000000) (ψ := -182979/200000) 277 269
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t443 : ((53605449721/5000000000000 : ℚ) : ℝ) ≤ stT277 443 := by
  have hc : ((225653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53605449721/5000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((225653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c444 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((752759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1796381/10000000) (δ := 1397/100000000) (ψ := -182979/200000) 277 269
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t444 : ((178609565901/5000000000000 : ℚ) : ℝ) ≤ stT277 444 := by
  have hc : ((752709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178609565901/5000000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((752709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c445 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((497727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238463/10000000) (δ := 14033/1000000000) (ψ := -182979/200000) 277 269
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t445 : ((23593314459/500000000000 : ℚ) : ℝ) ≤ stT277 445 := by
  have hc : ((248851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23593314459/500000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((248851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c446 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((864623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1315991/10000000) (δ := 1397/100000000) (ψ := -182979/200000) 277 269
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t446 : ((409386554949/10000000000000 : ℚ) : ℝ) ≤ stT277 446 := by
  have hc : ((864573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409386554949/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((864573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c447 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((205719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1433457/5000000) (δ := 1397/100000000) (ψ := -182979/200000) 277 269
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t447 : ((48644882601/2500000000000 : ℚ) : ℝ) ≤ stT277 447 := by
  have hc : ((102847/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48644882601/2500000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((102847/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c448 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-48437/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1103611/2500000) (δ := 1387/100000000) (ψ := -182979/200000) 277 269
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t448 : ((-5722564243/625000000000 : ℚ) : ℝ) ≤ stT277 448 := by
  have hc : ((-96899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5722564243/625000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-96899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c449 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-45379/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2979221/5000000) (δ := 1387/100000000) (ψ := -182979/200000) 277 269
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t449 : ((-17133749001/500000000000 : ℚ) : ℝ) ≤ stT277 449 := by
  have hc : ((-363057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17133749001/500000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-363057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c450 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-989939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7499047/10000000) (δ := 13933/1000000000) (ψ := -182979/200000) 277 269
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t450 : ((-93337152909/2000000000000 : ℚ) : ℝ) ≤ stT277 450 := by
  have hc : ((-989989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93337152909/2000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-989989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c451 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-445123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1334341/2000000) (δ := 13863/1000000000) (ψ := -182979/200000) 277 270
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t451 : ((-26201522567/625000000000 : ℚ) : ℝ) ≤ stT277 451 := by
  have hc : ((-111287/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26201522567/625000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-111287/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c452 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-93133/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1284489/2500000) (δ := 13863/1000000000) (ψ := -182979/200000) 277 270
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t452 : ((-43810834623/2000000000000 : ℚ) : ℝ) ≤ stT277 452 := by
  have hc : ((-93143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43810834623/2000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-93143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c453 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((31859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3607531/10000000) (δ := 13863/1000000000) (ψ := -182979/200000) 277 270
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t453 : ((374068989/62500000000 : ℚ) : ℝ) ≤ stT277 453 := by
  have hc : ((63693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374068989/62500000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((63693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c454 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((673231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -260071/1250000) (δ := 351/25000000) (ψ := -182979/200000) 277 270
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t454 : ((315939326463/10000000000000 : ℚ) : ℝ) ≤ stT277 454 := by
  have hc : ((673181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315939326463/10000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((673181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c455 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((195059/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -556861/10000000) (δ := 13963/1000000000) (ψ := -182979/200000) 277 270
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t455 : ((91440336543/2000000000000 : ℚ) : ℝ) ≤ stT277 455 := by
  have hc : ((195049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91440336543/2000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((195049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c456 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((185331/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 481727/5000000) (δ := 697/50000000) (ψ := -182979/200000) 277 270
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t456 : ((21696085433/500000000000 : ℚ) : ℝ) ≤ stT277 456 := by
  have hc : ((185321/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21696085433/500000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((185321/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c457 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((546891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19843/80000) (δ := 13863/1000000000) (ψ := -182979/200000) 277 270
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t457 : ((12790064149/500000000000 : ℚ) : ℝ) ≤ stT277 457 := by
  have hc : ((546841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12790064149/500000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((546841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c458 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-26817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1997021/5000000) (δ := 351/25000000) (ψ := -182979/200000) 277 270
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t458 : ((-1255414309/1000000000000 : ℚ) : ℝ) ≤ stT277 458 := by
  have hc : ((-26867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1255414309/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-26867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c459 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-29497/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5504453/10000000) (δ := 13963/1000000000) (ψ := -182979/200000) 277 270
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t459 : ((-27538432239/1000000000000 : ℚ) : ℝ) ≤ stT277 459 := by
  have hc : ((-58999/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27538432239/1000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-58999/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c460 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-151/160 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 438217/625000) (δ := 697/50000000) (ψ := -182979/200000) 277 270
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t460 : ((-2200247907/50000000000 : ℚ) : ℝ) ≤ stT277 460 := by
  have hc : ((-4719/5000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2200247907/50000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-4719/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c461 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-30163/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3596329/5000000) (δ := 14047/1000000000) (ψ := -182979/200000) 277 271
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t461 : ((-224784871851/5000000000000 : ℚ) : ℝ) ≤ stT277 461 := by
  have hc : ((-482633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224784871851/5000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-482633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c462 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-648843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5692149/10000000) (δ := 14047/1000000000) (ψ := -182979/200000) 277 271
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t462 : ((-301892925999/10000000000000 : ℚ) : ℝ) ≤ stT277 462 := by
  have hc : ((-648893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301892925999/10000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-648893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c463 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-106929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2097413/5000000) (δ := 433/31250000) (ψ := -182979/200000) 277 271
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t463 : ((-2485871023/500000000000 : ℚ) : ℝ) ≤ stT277 463 := by
  have hc : ((-106979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2485871023/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-106979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c464 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((471061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2700757/10000000) (δ := 13947/1000000000) (ψ := -182979/200000) 277 271
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t464 : ((109330602309/5000000000000 : ℚ) : ℝ) ≤ stT277 464 := by
  have hc : ((471011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109330602309/5000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((471011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c465 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((221291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604937/5000000) (δ := 433/31250000) (ψ := -182979/200000) 277 271
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t465 : ((102615249033/2500000000000 : ℚ) : ℝ) ≤ stT277 465 := by
  have hc : ((442557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102615249033/2500000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((442557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c466 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((198767/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55551/2000000) (δ := 14047/1000000000) (ψ := -182979/200000) 277 271
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t466 : ((92072391437/2000000000000 : ℚ) : ℝ) ≤ stT277 466 := by
  have hc : ((198757/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92072391437/2000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((198757/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c467 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((76169/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881099/5000000) (δ := 14047/1000000000) (ψ := -182979/200000) 277 271
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t467 : ((1101388563/31250000000 : ℚ) : ℝ) ≤ stT277 467 := by
  have hc : ((19041/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1101388563/31250000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((19041/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c468 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((270021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 648691/2000000) (δ := 433/31250000) (ψ := -182979/200000) 277 271
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t468 : ((499176379/40000000000 : ℚ) : ℝ) ≤ stT277 468 := by
  have hc : ((269971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499176379/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((269971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c469 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-312517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1180399/2500000) (δ := 3489/250000000) (ψ := -182979/200000) 277 271
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t469 : ((-72165156393/5000000000000 : ℚ) : ℝ) ≤ stT277 469 := by
  have hc : ((-312567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72165156393/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-312567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c470 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-788167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774569/1250000) (δ := 433/31250000) (ψ := -182979/200000) 277 271
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t470 : ((-181788851361/5000000000000 : ℚ) : ℝ) ≤ stT277 470 := by
  have hc : ((-788217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181788851361/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-788217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c471 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-498623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 958549/1250000) (δ := 14047/1000000000) (ψ := -182979/200000) 277 271
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t471 : ((-3590078607/78125000000 : ℚ) : ℝ) ≤ stT277 471 := by
  have hc : ((-62331/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3590078607/78125000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-62331/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c472 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-54447/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6570849/10000000) (δ := 14049/1000000000) (ψ := -182979/200000) 277 272
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t472 : ((-391605299/9765625000 : ℚ) : ℝ) ≤ stT277 472 := by
  have hc : ((-435601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391605299/9765625000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-435601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c473 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-90809/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2552621/5000000) (δ := 14049/1000000000) (ψ := -182979/200000) 277 272
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t473 : ((-41758667019/2000000000000 : ℚ) : ℝ) ≤ stT277 473 := by
  have hc : ((-90819/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41758667019/2000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-90819/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c474 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((113479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1821341/5000000) (δ := 14049/1000000000) (ψ := -182979/200000) 277 272
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t474 : ((10419928227/2000000000000 : ℚ) : ℝ) ≤ stT277 474 := by
  have hc : ((113429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10419928227/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((113429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c475 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((10036/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1091619/5000000) (δ := 13949/1000000000) (ψ := -182979/200000) 277 272
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t475 : ((147343022537/5000000000000 : ℚ) : ℝ) ≤ stT277 475 := by
  have hc : ((321127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147343022537/5000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((321127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c476 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((38321/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72691/1000000) (δ := 6977/500000000) (ψ := -182979/200000) 277 272
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t476 : ((17563475331/400000000000 : ℚ) : ℝ) ≤ stT277 476 := by
  have hc : ((38319/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17563475331/400000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((38319/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c477 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((958087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72637/1000000) (δ := 13949/1000000000) (ψ := -182979/200000) 277 272
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t477 : ((109663621279/2500000000000 : ℚ) : ℝ) ≤ stT277 477 := by
  have hc : ((958037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109663621279/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((958037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c478 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((128863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2176673/10000000) (δ := 6927/500000000) (ψ := -182979/200000) 277 272
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t478 : ((58935944817/2000000000000 : ℚ) : ℝ) ≤ stT277 478 := by
  have hc : ((128853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58935944817/2000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((128853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c479 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((30239/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3623859/10000000) (δ := 14049/1000000000) (ψ := -182979/200000) 277 272
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t479 : ((27621640683/5000000000000 : ℚ) : ℝ) ≤ stT277 479 := by
  have hc : ((60453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27621640683/5000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((60453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c480 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-110193/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5068137/10000000) (δ := 14049/1000000000) (ψ := -182979/200000) 277 272
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t480 : ((-25150878799/1250000000000 : ℚ) : ℝ) ≤ stT277 480 := by
  have hc : ((-220411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25150878799/1250000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-220411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c481 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-2147/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6509299/10000000) (δ := 13949/1000000000) (ψ := -182979/200000) 277 272
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t481 : ((-7832042097/200000000000 : ℚ) : ℝ) ≤ stT277 481 := by
  have hc : ((-17177/20000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7832042097/200000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-17177/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c482 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-9993/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7760411/10000000) (δ := 13941/1000000000) (ψ := -182979/200000) 277 273
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t482 : ((-142247479/3125000000 : ℚ) : ℝ) ≤ stT277 482 := by
  have hc : ((-19987/20000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142247479/3125000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-19987/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c483 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-409391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1265041/2000000) (δ := 14041/1000000000) (ψ := -182979/200000) 277 273
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t483 : ((-2910794229/78125000000 : ℚ) : ℝ) ≤ stT277 483 := by
  have hc : ((-51177/62500 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2910794229/78125000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-51177/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c484 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-15073/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4892907/10000000) (δ := 13941/1000000000) (ψ := -182979/200000) 277 273
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t484 : ((-137045619/8000000000 : ℚ) : ℝ) ≤ stT277 484 := by
  have hc : ((-603/1600 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137045619/8000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-603/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c485 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((7371/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -432957/1250000) (δ := 6931/500000000) (ψ := -182979/200000) 277 273
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t485 : ((836521511/100000000000 : ℚ) : ℝ) ≤ stT277 485 := by
  have hc : ((7369/40000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((836521511/100000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((7369/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c486 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((685943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -407449/2000000) (δ := 14041/1000000000) (ψ := -182979/200000) 277 273
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t486 : ((311127237837/10000000000000 : ℚ) : ℝ) ≤ stT277 486 := by
  have hc : ((685893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311127237837/10000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((685893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c487 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((97001/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -613811/10000000) (δ := 13941/1000000000) (ψ := -182979/200000) 277 273
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t487 : ((10988264607/250000000000 : ℚ) : ℝ) ≤ stT277 487 := by
  have hc : ((24249/25000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10988264607/250000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((24249/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c488 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((948387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403357/5000000) (δ := 14041/1000000000) (ψ := -182979/200000) 277 273
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t488 : ((214645648243/5000000000000 : ℚ) : ℝ) ≤ stT277 488 := by
  have hc : ((948337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214645648243/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((948337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c489 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((629641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1112131/5000000) (δ := 6931/500000000) (ψ := -182979/200000) 277 273
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t489 : ((56942098813/2000000000000 : ℚ) : ℝ) ≤ stT277 489 := by
  have hc : ((629591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56942098813/2000000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((629591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c490 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((57477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363897/1000000) (δ := 13941/1000000000) (ψ := -182979/200000) 277 273
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t490 : ((6488528339/1250000000000 : ℚ) : ℝ) ≤ stT277 490 := by
  have hc : ((14363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6488528339/1250000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((14363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c491 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-434551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5050839/10000000) (δ := 13941/1000000000) (ψ := -182979/200000) 277 273
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t491 : ((-98066411847/5000000000000 : ℚ) : ℝ) ≤ stT277 491 := by
  have hc : ((-434601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98066411847/5000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-434601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c492 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-848489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32299/50000) (δ := 6981/500000000) (ψ := -182979/200000) 277 273
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t492 : ((-76510216013/2000000000000 : ℚ) : ℝ) ≤ stT277 492 := by
  have hc : ((-848539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76510216013/2000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-848539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c493 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-999989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122533/156250) (δ := 7017/500000000) (ψ := -182979/200000) 277 274
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t493 : ((-225197782371/5000000000000 : ℚ) : ℝ) ≤ stT277 493 := by
  have hc : ((-1000039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225197782371/5000000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-1000039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c494 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-42201/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -643883/1000000) (δ := 7017/500000000) (ψ := -182979/200000) 277 274
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t494 : ((-18988283127/500000000000 : ℚ) : ℝ) ≤ stT277 494 := by
  have hc : ((-84407/100000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18988283127/500000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-84407/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c495 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((-107521/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -629807/1250000) (δ := 13869/1000000000) (ψ := -182979/200000) 277 274
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t495 : ((-96665519289/5000000000000 : ℚ) : ℝ) ≤ stT277 495 := by
  have hc : ((-215067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96665519289/5000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-215067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c496 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((22841/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3640853/10000000) (δ := 7017/500000000) (ψ := -182979/200000) 277 274
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t496 : ((10251415803/2000000000000 : ℚ) : ℝ) ≤ stT277 496 := by
  have hc : ((22831/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10251415803/2000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((22831/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c497 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((124567/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -280761/1250000) (δ := 13969/1000000000) (ψ := -182979/200000) 277 274
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t497 : ((55871412477/2000000000000 : ℚ) : ℝ) ≤ stT277 497 := by
  have hc : ((124557/200000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55871412477/2000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((124557/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c498 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((471099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -854163/10000000) (δ := 13969/1000000000) (ψ := -182979/200000) 277 274
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t498 : ((10554648507/250000000000 : ℚ) : ℝ) ≤ stT277 498 := by
  have hc : ((235537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10554648507/250000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((235537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c499 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((97719/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33437/625000) (δ := 13969/1000000000) (ψ := -182979/200000) 277 274
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t499 : ((21871373477/500000000000 : ℚ) : ℝ) ≤ stT277 499 := by
  have hc : ((48857/50000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21871373477/500000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((48857/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_c500 :
    |Real.cos (((277 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((718919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1921377/10000000) (δ := 13969/1000000000) (ψ := -182979/200000) 277 274
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st277_t500 : ((321487562097/10000000000000 : ℚ) : ℝ) ≤ stT277 500 := by
  have hc : ((718869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((277 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st277_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321487562097/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((718869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st277_p1 : ((19057/31250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT277 (i+1) := by
  rw [Finset.sum_range_one]
  exact st277_t1

theorem st277_p2 : ((25419665173/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT277 (i+1))
      = (∑ i ∈ Finset.range 1, stT277 (i+1)) + stT277 2 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 1
    simpa using h
  have hprev := st277_p1
  have hstep := st277_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p3 : ((-1010897721449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT277 (i+1))
      = (∑ i ∈ Finset.range 2, stT277 (i+1)) + stT277 3 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 2
    simpa using h
  have hprev := st277_p2
  have hstep := st277_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p4 : ((-1377467794763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT277 (i+1))
      = (∑ i ∈ Finset.range 3, stT277 (i+1)) + stT277 4 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 3
    simpa using h
  have hprev := st277_p3
  have hstep := st277_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p5 : ((2254138376257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT277 (i+1))
      = (∑ i ∈ Finset.range 4, stT277 (i+1)) + stT277 5 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 4
    simpa using h
  have hprev := st277_p4
  have hstep := st277_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p6 : ((4915569629287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT277 (i+1))
      = (∑ i ∈ Finset.range 5, stT277 (i+1)) + stT277 6 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 5
    simpa using h
  have hprev := st277_p5
  have hstep := st277_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p7 : ((8363549868287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT277 (i+1))
      = (∑ i ∈ Finset.range 6, stT277 (i+1)) + stT277 7 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 6
    simpa using h
  have hprev := st277_p6
  have hstep := st277_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p8 : ((394509725579/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT277 (i+1))
      = (∑ i ∈ Finset.range 7, stT277 (i+1)) + stT277 8 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 7
    simpa using h
  have hprev := st277_p7
  have hstep := st277_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p9 : ((13186002807149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT277 (i+1))
      = (∑ i ∈ Finset.range 8, stT277 (i+1)) + stT277 9 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 8
    simpa using h
  have hprev := st277_p8
  have hstep := st277_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p10 : ((11444514176603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT277 (i+1))
      = (∑ i ∈ Finset.range 9, stT277 (i+1)) + stT277 10 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 9
    simpa using h
  have hprev := st277_p9
  have hstep := st277_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p11 : ((667601120047/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT277 (i+1))
      = (∑ i ∈ Finset.range 10, stT277 (i+1)) + stT277 11 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 10
    simpa using h
  have hprev := st277_p10
  have hstep := st277_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p12 : ((618704592983/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT277 (i+1))
      = (∑ i ∈ Finset.range 11, stT277 (i+1)) + stT277 12 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 11
    simpa using h
  have hprev := st277_p11
  have hstep := st277_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p13 : ((80182211701/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT277 (i+1))
      = (∑ i ∈ Finset.range 12, stT277 (i+1)) + stT277 13 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 12
    simpa using h
  have hprev := st277_p12
  have hstep := st277_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p14 : ((1270099459007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT277 (i+1))
      = (∑ i ∈ Finset.range 13, stT277 (i+1)) + stT277 14 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 13
    simpa using h
  have hprev := st277_p13
  have hstep := st277_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p15 : ((954038185517/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT277 (i+1))
      = (∑ i ∈ Finset.range 14, stT277 (i+1)) + stT277 15 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 14
    simpa using h
  have hprev := st277_p14
  have hstep := st277_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p16 : ((2917154882469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT277 (i+1))
      = (∑ i ∈ Finset.range 15, stT277 (i+1)) + stT277 16 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 15
    simpa using h
  have hprev := st277_p15
  have hstep := st277_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p17 : ((4069414839153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT277 (i+1))
      = (∑ i ∈ Finset.range 16, stT277 (i+1)) + stT277 17 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 16
    simpa using h
  have hprev := st277_p16
  have hstep := st277_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p18 : ((1501986044743/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT277 (i+1))
      = (∑ i ∈ Finset.range 17, stT277 (i+1)) + stT277 18 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 17
    simpa using h
  have hprev := st277_p17
  have hstep := st277_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p19 : ((8206450891171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT277 (i+1))
      = (∑ i ∈ Finset.range 18, stT277 (i+1)) + stT277 19 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 18
    simpa using h
  have hprev := st277_p18
  have hstep := st277_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p20 : ((8691104997019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT277 (i+1))
      = (∑ i ∈ Finset.range 19, stT277 (i+1)) + stT277 20 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 19
    simpa using h
  have hprev := st277_p19
  have hstep := st277_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p21 : ((1808947545577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT277 (i+1))
      = (∑ i ∈ Finset.range 20, stT277 (i+1)) + stT277 21 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 20
    simpa using h
  have hprev := st277_p20
  have hstep := st277_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p22 : ((1346673844973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT277 (i+1))
      = (∑ i ∈ Finset.range 21, stT277 (i+1)) + stT277 22 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 21
    simpa using h
  have hprev := st277_p21
  have hstep := st277_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p23 : ((3895989771927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT277 (i+1))
      = (∑ i ∈ Finset.range 22, stT277 (i+1)) + stT277 23 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 22
    simpa using h
  have hprev := st277_p22
  have hstep := st277_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p24 : ((771391836729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT277 (i+1))
      = (∑ i ∈ Finset.range 23, stT277 (i+1)) + stT277 24 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 23
    simpa using h
  have hprev := st277_p23
  have hstep := st277_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p25 : ((1149633836729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT277 (i+1))
      = (∑ i ∈ Finset.range 24, stT277 (i+1)) + stT277 25 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 24
    simpa using h
  have hprev := st277_p24
  have hstep := st277_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p26 : ((6137216458181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT277 (i+1))
      = (∑ i ∈ Finset.range 25, stT277 (i+1)) + stT277 26 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 25
    simpa using h
  have hprev := st277_p25
  have hstep := st277_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p27 : ((864784164793/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT277 (i+1))
      = (∑ i ∈ Finset.range 26, stT277 (i+1)) + stT277 27 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 26
    simpa using h
  have hprev := st277_p26
  have hstep := st277_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p28 : ((6125108282343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT277 (i+1))
      = (∑ i ∈ Finset.range 27, stT277 (i+1)) + stT277 28 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 27
    simpa using h
  have hprev := st277_p27
  have hstep := st277_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p29 : ((4595375574499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT277 (i+1))
      = (∑ i ∈ Finset.range 28, stT277 (i+1)) + stT277 29 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 28
    simpa using h
  have hprev := st277_p28
  have hstep := st277_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p30 : ((1533398351149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT277 (i+1))
      = (∑ i ∈ Finset.range 29, stT277 (i+1)) + stT277 30 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 29
    simpa using h
  have hprev := st277_p29
  have hstep := st277_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p31 : ((2191720578337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT277 (i+1))
      = (∑ i ∈ Finset.range 30, stT277 (i+1)) + stT277 31 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 30
    simpa using h
  have hprev := st277_p30
  have hstep := st277_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p32 : ((3004542920669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT277 (i+1))
      = (∑ i ∈ Finset.range 31, stT277 (i+1)) + stT277 32 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 31
    simpa using h
  have hprev := st277_p31
  have hstep := st277_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p33 : ((2775568077197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT277 (i+1))
      = (∑ i ∈ Finset.range 32, stT277 (i+1)) + stT277 33 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 32
    simpa using h
  have hprev := st277_p32
  have hstep := st277_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p34 : ((105477277333/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT277 (i+1))
      = (∑ i ∈ Finset.range 33, stT277 (i+1)) + stT277 34 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 33
    simpa using h
  have hprev := st277_p33
  have hstep := st277_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p35 : ((1374172105279/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT277 (i+1))
      = (∑ i ∈ Finset.range 34, stT277 (i+1)) + stT277 35 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 34
    simpa using h
  have hprev := st277_p34
  have hstep := st277_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p36 : ((1662536989933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT277 (i+1))
      = (∑ i ∈ Finset.range 35, stT277 (i+1)) + stT277 36 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 35
    simpa using h
  have hprev := st277_p35
  have hstep := st277_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p37 : ((2901071696971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT277 (i+1))
      = (∑ i ∈ Finset.range 36, stT277 (i+1)) + stT277 37 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 36
    simpa using h
  have hprev := st277_p36
  have hstep := st277_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p38 : ((1046102237943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT277 (i+1))
      = (∑ i ∈ Finset.range 37, stT277 (i+1)) + stT277 38 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 37
    simpa using h
  have hprev := st277_p37
  have hstep := st277_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p39 : ((825442375779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT277 (i+1))
      = (∑ i ∈ Finset.range 38, stT277 (i+1)) + stT277 39 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 38
    simpa using h
  have hprev := st277_p38
  have hstep := st277_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p40 : ((1765932305283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT277 (i+1))
      = (∑ i ∈ Finset.range 39, stT277 (i+1)) + stT277 40 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 39
    simpa using h
  have hprev := st277_p39
  have hstep := st277_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p41 : ((4541176190241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT277 (i+1))
      = (∑ i ∈ Finset.range 40, stT277 (i+1)) + stT277 41 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 40
    simpa using h
  have hprev := st277_p40
  have hstep := st277_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p42 : ((1478117018577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT277 (i+1))
      = (∑ i ∈ Finset.range 41, stT277 (i+1)) + stT277 42 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 41
    simpa using h
  have hprev := st277_p41
  have hstep := st277_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p43 : ((924143651261/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT277 (i+1))
      = (∑ i ∈ Finset.range 42, stT277 (i+1)) + stT277 43 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 42
    simpa using h
  have hprev := st277_p42
  have hstep := st277_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p44 : ((277568795867/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT277 (i+1))
      = (∑ i ∈ Finset.range 43, stT277 (i+1)) + stT277 44 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 43
    simpa using h
  have hprev := st277_p43
  have hstep := st277_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p45 : ((5169299640973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT277 (i+1))
      = (∑ i ∈ Finset.range 44, stT277 (i+1)) + stT277 45 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 44
    simpa using h
  have hprev := st277_p44
  have hstep := st277_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p46 : ((11690881835243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT277 (i+1))
      = (∑ i ∈ Finset.range 45, stT277 (i+1)) + stT277 46 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 45
    simpa using h
  have hprev := st277_p45
  have hstep := st277_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p47 : ((12772187090837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT277 (i+1))
      = (∑ i ∈ Finset.range 46, stT277 (i+1)) + stT277 47 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 46
    simpa using h
  have hprev := st277_p46
  have hstep := st277_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p48 : ((6656220454981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT277 (i+1))
      = (∑ i ∈ Finset.range 47, stT277 (i+1)) + stT277 48 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 47
    simpa using h
  have hprev := st277_p47
  have hstep := st277_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p49 : ((6522708258719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT277 (i+1))
      = (∑ i ∈ Finset.range 48, stT277 (i+1)) + stT277 49 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 48
    simpa using h
  have hprev := st277_p48
  have hstep := st277_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p50 : ((1195989130689/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT277 (i+1))
      = (∑ i ∈ Finset.range 49, stT277 (i+1)) + stT277 50 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 49
    simpa using h
  have hprev := st277_p49
  have hstep := st277_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p51 : ((10566825954883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT277 (i+1))
      = (∑ i ∈ Finset.range 50, stT277 (i+1)) + stT277 51 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 50
    simpa using h
  have hprev := st277_p50
  have hstep := st277_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p52 : ((2456250383799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT277 (i+1))
      = (∑ i ∈ Finset.range 51, stT277 (i+1)) + stT277 52 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 51
    simpa using h
  have hprev := st277_p51
  have hstep := st277_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p53 : ((5206530533083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT277 (i+1))
      = (∑ i ∈ Finset.range 52, stT277 (i+1)) + stT277 53 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 52
    simpa using h
  have hprev := st277_p52
  have hstep := st277_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p54 : ((11773464848969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT277 (i+1))
      = (∑ i ∈ Finset.range 53, stT277 (i+1)) + stT277 54 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 53
    simpa using h
  have hprev := st277_p53
  have hstep := st277_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p55 : ((12289998750697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT277 (i+1))
      = (∑ i ∈ Finset.range 54, stT277 (i+1)) + stT277 55 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 54
    simpa using h
  have hprev := st277_p54
  have hstep := st277_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p56 : ((11244092642709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT277 (i+1))
      = (∑ i ∈ Finset.range 55, stT277 (i+1)) + stT277 56 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 55
    simpa using h
  have hprev := st277_p55
  have hstep := st277_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p57 : ((409529797263/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT277 (i+1))
      = (∑ i ∈ Finset.range 56, stT277 (i+1)) + stT277 57 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 56
    simpa using h
  have hprev := st277_p56
  have hstep := st277_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p58 : ((10983213105039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT277 (i+1))
      = (∑ i ∈ Finset.range 57, stT277 (i+1)) + stT277 58 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 57
    simpa using h
  have hprev := st277_p57
  have hstep := st277_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p59 : ((6035855390469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT277 (i+1))
      = (∑ i ∈ Finset.range 58, stT277 (i+1)) + stT277 59 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 58
    simpa using h
  have hprev := st277_p58
  have hstep := st277_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p60 : ((11303355741763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT277 (i+1))
      = (∑ i ∈ Finset.range 59, stT277 (i+1)) + stT277 60 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 59
    simpa using h
  have hprev := st277_p59
  have hstep := st277_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p61 : ((1038515575821/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT277 (i+1))
      = (∑ i ∈ Finset.range 60, stT277 (i+1)) + stT277 61 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 60
    simpa using h
  have hprev := st277_p60
  have hstep := st277_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p62 : ((1143940898833/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT277 (i+1))
      = (∑ i ∈ Finset.range 61, stT277 (i+1)) + stT277 62 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 61
    simpa using h
  have hprev := st277_p61
  have hstep := st277_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p63 : ((1478126335869/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT277 (i+1))
      = (∑ i ∈ Finset.range 62, stT277 (i+1)) + stT277 63 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 62
    simpa using h
  have hprev := st277_p62
  have hstep := st277_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p64 : ((10575898437663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT277 (i+1))
      = (∑ i ∈ Finset.range 63, stT277 (i+1)) + stT277 64 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 63
    simpa using h
  have hprev := st277_p63
  have hstep := st277_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p65 : ((5561424026259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT277 (i+1))
      = (∑ i ∈ Finset.range 64, stT277 (i+1)) + stT277 65 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 64
    simpa using h
  have hprev := st277_p64
  have hstep := st277_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p66 : ((1481092985939/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT277 (i+1))
      = (∑ i ∈ Finset.range 65, stT277 (i+1)) + stT277 66 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 65
    simpa using h
  have hprev := st277_p65
  have hstep := st277_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p67 : ((5315641641191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT277 (i+1))
      = (∑ i ∈ Finset.range 66, stT277 (i+1)) + stT277 67 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 66
    simpa using h
  have hprev := st277_p66
  have hstep := st277_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p68 : ((5619370185749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT277 (i+1))
      = (∑ i ∈ Finset.range 67, stT277 (i+1)) + stT277 68 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 67
    simpa using h
  have hprev := st277_p67
  have hstep := st277_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p69 : ((2920619704681/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT277 (i+1))
      = (∑ i ∈ Finset.range 68, stT277 (i+1)) + stT277 69 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 68
    simpa using h
  have hprev := st277_p68
  have hstep := st277_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p70 : ((1319914070699/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT277 (i+1))
      = (∑ i ∈ Finset.range 69, stT277 (i+1)) + stT277 70 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 69
    simpa using h
  have hprev := st277_p69
  have hstep := st277_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p71 : ((1454226823593/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT277 (i+1))
      = (∑ i ∈ Finset.range 70, stT277 (i+1)) + stT277 71 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 70
    simpa using h
  have hprev := st277_p70
  have hstep := st277_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p72 : ((279375732381/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT277 (i+1))
      = (∑ i ∈ Finset.range 71, stT277 (i+1)) + stT277 72 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 71
    simpa using h
  have hprev := st277_p71
  have hstep := st277_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p73 : ((339133128011/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT277 (i+1))
      = (∑ i ∈ Finset.range 72, stT277 (i+1)) + stT277 73 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 72
    simpa using h
  have hprev := st277_p72
  have hstep := st277_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p74 : ((1470934972013/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT277 (i+1))
      = (∑ i ∈ Finset.range 73, stT277 (i+1)) + stT277 74 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 73
    simpa using h
  have hprev := st277_p73
  have hstep := st277_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p75 : ((1327144675287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT277 (i+1))
      = (∑ i ∈ Finset.range 74, stT277 (i+1)) + stT277 75 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 74
    simpa using h
  have hprev := st277_p74
  have hstep := st277_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p76 : ((5827548332993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT277 (i+1))
      = (∑ i ∈ Finset.range 75, stT277 (i+1)) + stT277 76 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 75
    simpa using h
  have hprev := st277_p75
  have hstep := st277_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p77 : ((137046919331/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT277 (i+1))
      = (∑ i ∈ Finset.range 76, stT277 (i+1)) + stT277 77 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 76
    simpa using h
  have hprev := st277_p76
  have hstep := st277_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p78 : ((11209830174613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT277 (i+1))
      = (∑ i ∈ Finset.range 77, stT277 (i+1)) + stT277 78 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 77
    simpa using h
  have hprev := st277_p77
  have hstep := st277_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p79 : ((5698940295527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT277 (i+1))
      = (∑ i ∈ Finset.range 78, stT277 (i+1)) + stT277 79 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 78
    simpa using h
  have hprev := st277_p78
  have hstep := st277_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p80 : ((5425663717043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT277 (i+1))
      = (∑ i ∈ Finset.range 79, stT277 (i+1)) + stT277 80 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 79
    simpa using h
  have hprev := st277_p79
  have hstep := st277_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p81 : ((11656155131381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT277 (i+1))
      = (∑ i ∈ Finset.range 80, stT277 (i+1)) + stT277 81 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 80
    simpa using h
  have hprev := st277_p80
  have hstep := st277_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p82 : ((10688785358541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT277 (i+1))
      = (∑ i ∈ Finset.range 81, stT277 (i+1)) + stT277 82 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 81
    simpa using h
  have hprev := st277_p81
  have hstep := st277_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p83 : ((11741358178021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT277 (i+1))
      = (∑ i ∈ Finset.range 82, stT277 (i+1)) + stT277 83 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 82
    simpa using h
  have hprev := st277_p82
  have hstep := st277_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p84 : ((10656998021141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT277 (i+1))
      = (∑ i ∈ Finset.range 83, stT277 (i+1)) + stT277 84 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 83
    simpa using h
  have hprev := st277_p83
  have hstep := st277_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p85 : ((11741257377117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT277 (i+1))
      = (∑ i ∈ Finset.range 84, stT277 (i+1)) + stT277 85 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 84
    simpa using h
  have hprev := st277_p84
  have hstep := st277_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p86 : ((2134208974729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT277 (i+1))
      = (∑ i ∈ Finset.range 85, stT277 (i+1)) + stT277 86 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 85
    simpa using h
  have hprev := st277_p85
  have hstep := st277_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p87 : ((11725015666493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT277 (i+1))
      = (∑ i ∈ Finset.range 86, stT277 (i+1)) + stT277 87 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 86
    simpa using h
  have hprev := st277_p86
  have hstep := st277_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p88 : ((10681958468597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT277 (i+1))
      = (∑ i ∈ Finset.range 87, stT277 (i+1)) + stT277 88 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 87
    simpa using h
  have hprev := st277_p87
  have hstep := st277_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p89 : ((366297162077/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT277 (i+1))
      = (∑ i ∈ Finset.range 88, stT277 (i+1)) + stT277 89 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 88
    simpa using h
  have hprev := st277_p88
  have hstep := st277_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p90 : ((1067918197253/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT277 (i+1))
      = (∑ i ∈ Finset.range 89, stT277 (i+1)) + stT277 90 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 89
    simpa using h
  have hprev := st277_p89
  have hstep := st277_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p91 : ((5862456176353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT277 (i+1))
      = (∑ i ∈ Finset.range 90, stT277 (i+1)) + stT277 91 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 90
    simpa using h
  have hprev := st277_p90
  have hstep := st277_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p92 : ((10683349605943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT277 (i+1))
      = (∑ i ∈ Finset.range 91, stT277 (i+1)) + stT277 92 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 91
    simpa using h
  have hprev := st277_p91
  have hstep := st277_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p93 : ((2340234186779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT277 (i+1))
      = (∑ i ∈ Finset.range 92, stT277 (i+1)) + stT277 93 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 92
    simpa using h
  have hprev := st277_p92
  have hstep := st277_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p94 : ((10739912446867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT277 (i+1))
      = (∑ i ∈ Finset.range 93, stT277 (i+1)) + stT277 94 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 93
    simpa using h
  have hprev := st277_p93
  have hstep := st277_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p95 : ((11597228897469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT277 (i+1))
      = (∑ i ∈ Finset.range 94, stT277 (i+1)) + stT277 95 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 94
    simpa using h
  have hprev := st277_p94
  have hstep := st277_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p96 : ((10902761626713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT277 (i+1))
      = (∑ i ∈ Finset.range 95, stT277 (i+1)) + stT277 96 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 95
    simpa using h
  have hprev := st277_p95
  have hstep := st277_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p97 : ((2273809215543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT277 (i+1))
      = (∑ i ∈ Finset.range 96, stT277 (i+1)) + stT277 97 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 96
    simpa using h
  have hprev := st277_p96
  have hstep := st277_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p98 : ((2797869588229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT277 (i+1))
      = (∑ i ∈ Finset.range 97, stT277 (i+1)) + stT277 98 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 97
    simpa using h
  have hprev := st277_p97
  have hstep := st277_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p99 : ((5519263322443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT277 (i+1))
      = (∑ i ∈ Finset.range 98, stT277 (i+1)) + stT277 99 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 98
    simpa using h
  have hprev := st277_p98
  have hstep := st277_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p100 : ((11526991156421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT277 (i+1))
      = (∑ i ∈ Finset.range 99, stT277 (i+1)) + stT277 100 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 99
    simpa using h
  have hprev := st277_p99
  have hstep := st277_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p101 : ((10750156034479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT277 (i+1))
      = (∑ i ∈ Finset.range 100, stT277 (i+1)) + stT277 101 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 100
    simpa using h
  have hprev := st277_p100
  have hstep := st277_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p102 : ((11706317228851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT277 (i+1))
      = (∑ i ∈ Finset.range 101, stT277 (i+1)) + stT277 102 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 101
    simpa using h
  have hprev := st277_p101
  have hstep := st277_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p103 : ((10736259843851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT277 (i+1))
      = (∑ i ∈ Finset.range 102, stT277 (i+1)) + stT277 103 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 102
    simpa using h
  have hprev := st277_p102
  have hstep := st277_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p104 : ((11521658336591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT277 (i+1))
      = (∑ i ∈ Finset.range 103, stT277 (i+1)) + stT277 104 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 103
    simpa using h
  have hprev := st277_p103
  have hstep := st277_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p105 : ((2776897105449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT277 (i+1))
      = (∑ i ∈ Finset.range 104, stT277 (i+1)) + stT277 105 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 104
    simpa using h
  have hprev := st277_p104
  have hstep := st277_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p106 : ((5515993216707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT277 (i+1))
      = (∑ i ∈ Finset.range 105, stT277 (i+1)) + stT277 106 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 105
    simpa using h
  have hprev := st277_p105
  have hstep := st277_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p107 : ((5796225814707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT277 (i+1))
      = (∑ i ∈ Finset.range 106, stT277 (i+1)) + stT277 107 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 106
    simpa using h
  have hprev := st277_p106
  have hstep := st277_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p108 : ((5350745940751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT277 (i+1))
      = (∑ i ∈ Finset.range 107, stT277 (i+1)) + stT277 108 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 107
    simpa using h
  have hprev := st277_p107
  have hstep := st277_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p109 : ((5819982982499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT277 (i+1))
      = (∑ i ∈ Finset.range 108, stT277 (i+1)) + stT277 109 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 108
    simpa using h
  have hprev := st277_p108
  have hstep := st277_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p110 : ((10984581242299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT277 (i+1))
      = (∑ i ∈ Finset.range 109, stT277 (i+1)) + stT277 110 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 109
    simpa using h
  have hprev := st277_p109
  have hstep := st277_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p111 : ((5550505742009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT277 (i+1))
      = (∑ i ∈ Finset.range 110, stT277 (i+1)) + stT277 111 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 110
    simpa using h
  have hprev := st277_p110
  have hstep := st277_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p112 : ((2895530119739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT277 (i+1))
      = (∑ i ∈ Finset.range 111, stT277 (i+1)) + stT277 112 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 111
    simpa using h
  have hprev := st277_p111
  have hstep := st277_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p113 : ((1337591108873/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT277 (i+1))
      = (∑ i ∈ Finset.range 112, stT277 (i+1)) + stT277 113 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 112
    simpa using h
  have hprev := st277_p112
  have hstep := st277_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p114 : ((11582438419249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT277 (i+1))
      = (∑ i ∈ Finset.range 113, stT277 (i+1)) + stT277 114 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 113
    simpa using h
  have hprev := st277_p113
  have hstep := st277_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p115 : ((2782896559831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT277 (i+1))
      = (∑ i ∈ Finset.range 114, stT277 (i+1)) + stT277 115 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 114
    simpa using h
  have hprev := st277_p114
  have hstep := st277_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p116 : ((681997768109/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT277 (i+1))
      = (∑ i ∈ Finset.range 115, stT277 (i+1)) + stT277 116 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 115
    simpa using h
  have hprev := st277_p115
  have hstep := st277_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p117 : ((730698116859/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT277 (i+1))
      = (∑ i ∈ Finset.range 116, stT277 (i+1)) + stT277 117 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 116
    simpa using h
  have hprev := st277_p116
  have hstep := st277_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p118 : ((2697983449561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT277 (i+1))
      = (∑ i ∈ Finset.range 117, stT277 (i+1)) + stT277 118 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 117
    simpa using h
  have hprev := st277_p117
  have hstep := st277_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p119 : ((2817912298807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT277 (i+1))
      = (∑ i ∈ Finset.range 118, stT277 (i+1)) + stT277 119 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 118
    simpa using h
  have hprev := st277_p118
  have hstep := st277_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p120 : ((359923291739/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT277 (i+1))
      = (∑ i ∈ Finset.range 119, stT277 (i+1)) + stT277 120 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 119
    simpa using h
  have hprev := st277_p119
  have hstep := st277_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p121 : ((5350486263359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT277 (i+1))
      = (∑ i ∈ Finset.range 120, stT277 (i+1)) + stT277 121 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 120
    simpa using h
  have hprev := st277_p120
  have hstep := st277_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p122 : ((11532485893727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT277 (i+1))
      = (∑ i ∈ Finset.range 121, stT277 (i+1)) + stT277 122 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 121
    simpa using h
  have hprev := st277_p121
  have hstep := st277_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p123 : ((11279900174957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT277 (i+1))
      = (∑ i ∈ Finset.range 122, stT277 (i+1)) + stT277 123 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 122
    simpa using h
  have hprev := st277_p122
  have hstep := st277_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p124 : ((5380942487179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT277 (i+1))
      = (∑ i ∈ Finset.range 123, stT277 (i+1)) + stT277 124 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 123
    simpa using h
  have hprev := st277_p123
  have hstep := st277_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p125 : ((11655575860937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT277 (i+1))
      = (∑ i ∈ Finset.range 124, stT277 (i+1)) + stT277 125 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 124
    simpa using h
  have hprev := st277_p124
  have hstep := st277_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p126 : ((11098321796501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT277 (i+1))
      = (∑ i ∈ Finset.range 125, stT277 (i+1)) + stT277 126 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 125
    simpa using h
  have hprev := st277_p125
  have hstep := st277_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p127 : ((1357041888227/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT277 (i+1))
      = (∑ i ∈ Finset.range 126, stT277 (i+1)) + stT277 127 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 126
    simpa using h
  have hprev := st277_p126
  have hstep := st277_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p128 : ((2338745702333/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT277 (i+1))
      = (∑ i ∈ Finset.range 127, stT277 (i+1)) + stT277 128 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 127
    simpa using h
  have hprev := st277_p127
  have hstep := st277_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p129 : ((549914994353/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT277 (i+1))
      = (∑ i ∈ Finset.range 128, stT277 (i+1)) + stT277 129 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 128
    simpa using h
  have hprev := st277_p128
  have hstep := st277_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p130 : ((10917586778467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT277 (i+1))
      = (∑ i ∈ Finset.range 129, stT277 (i+1)) + stT277 130 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 129
    simpa using h
  have hprev := st277_p129
  have hstep := st277_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p131 : ((93604292183/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT277 (i+1))
      = (∑ i ∈ Finset.range 130, stT277 (i+1)) + stT277 131 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 130
    simpa using h
  have hprev := st277_p130
  have hstep := st277_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p132 : ((219405167843/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT277 (i+1))
      = (∑ i ∈ Finset.range 131, stT277 (i+1)) + stT277 132 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 131
    simpa using h
  have hprev := st277_p131
  have hstep := st277_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p133 : ((1092201065753/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT277 (i+1))
      = (∑ i ∈ Finset.range 132, stT277 (i+1)) + stT277 133 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 132
    simpa using h
  have hprev := st277_p132
  have hstep := st277_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p134 : ((5850199891399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT277 (i+1))
      = (∑ i ∈ Finset.range 133, stT277 (i+1)) + stT277 134 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 133
    simpa using h
  have hprev := st277_p133
  have hstep := st277_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p135 : ((2201351236783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT277 (i+1))
      = (∑ i ∈ Finset.range 134, stT277 (i+1)) + stT277 135 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 134
    simpa using h
  have hprev := st277_p134
  have hstep := st277_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p136 : ((5434996026433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT277 (i+1))
      = (∑ i ∈ Finset.range 135, stT277 (i+1)) + stT277 136 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 135
    simpa using h
  have hprev := st277_p135
  have hstep := st277_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p137 : ((5843274440879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT277 (i+1))
      = (∑ i ∈ Finset.range 136, stT277 (i+1)) + stT277 137 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 136
    simpa using h
  have hprev := st277_p136
  have hstep := st277_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p138 : ((11111164696547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT277 (i+1))
      = (∑ i ∈ Finset.range 137, stT277 (i+1)) + stT277 138 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 137
    simpa using h
  have hprev := st277_p137
  have hstep := st277_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p139 : ((10781273459643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT277 (i+1))
      = (∑ i ∈ Finset.range 138, stT277 (i+1)) + stT277 139 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 138
    simpa using h
  have hprev := st277_p138
  have hstep := st277_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p140 : ((11626284628617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT277 (i+1))
      = (∑ i ∈ Finset.range 139, stT277 (i+1)) + stT277 140 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 139
    simpa using h
  have hprev := st277_p139
  have hstep := st277_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p141 : ((11285785731977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT277 (i+1))
      = (∑ i ∈ Finset.range 140, stT277 (i+1)) + stT277 141 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 140
    simpa using h
  have hprev := st277_p140
  have hstep := st277_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p142 : ((10702887397231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT277 (i+1))
      = (∑ i ∈ Finset.range 141, stT277 (i+1)) + stT277 142 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 141
    simpa using h
  have hprev := st277_p141
  have hstep := st277_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p143 : ((11474784756541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT277 (i+1))
      = (∑ i ∈ Finset.range 142, stT277 (i+1)) + stT277 143 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 142
    simpa using h
  have hprev := st277_p142
  have hstep := st277_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p144 : ((11504081411489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT277 (i+1))
      = (∑ i ∈ Finset.range 143, stT277 (i+1)) + stT277 144 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 143
    simpa using h
  have hprev := st277_p143
  have hstep := st277_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p145 : ((10713415171449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT277 (i+1))
      = (∑ i ∈ Finset.range 144, stT277 (i+1)) + stT277 145 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 144
    simpa using h
  have hprev := st277_p144
  have hstep := st277_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p146 : ((11210244660259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT277 (i+1))
      = (∑ i ∈ Finset.range 145, stT277 (i+1)) + stT277 146 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 145
    simpa using h
  have hprev := st277_p145
  have hstep := st277_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p147 : ((11680566504969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT277 (i+1))
      = (∑ i ∈ Finset.range 146, stT277 (i+1)) + stT277 147 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 146
    simpa using h
  have hprev := st277_p146
  have hstep := st277_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p148 : ((85118470753/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT277 (i+1))
      = (∑ i ∈ Finset.range 147, stT277 (i+1)) + stT277 148 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 147
    simpa using h
  have hprev := st277_p147
  have hstep := st277_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p149 : ((4254268433/3906250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT277 (i+1))
      = (∑ i ∈ Finset.range 148, stT277 (i+1)) + stT277 149 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 148
    simpa using h
  have hprev := st277_p148
  have hstep := st277_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p150 : ((22805231963/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT277 (i+1))
      = (∑ i ∈ Finset.range 149, stT277 (i+1)) + stT277 150 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 149
    simpa using h
  have hprev := st277_p149
  have hstep := st277_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p151 : ((5626599000923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT277 (i+1))
      = (∑ i ∈ Finset.range 150, stT277 (i+1)) + stT277 151 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 150
    simpa using h
  have hprev := st277_p150
  have hstep := st277_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p152 : ((5345269030001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT277 (i+1))
      = (∑ i ∈ Finset.range 151, stT277 (i+1)) + stT277 152 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 151
    simpa using h
  have hprev := st277_p151
  have hstep := st277_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p153 : ((5695856665157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT277 (i+1))
      = (∑ i ∈ Finset.range 152, stT277 (i+1)) + stT277 153 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 152
    simpa using h
  have hprev := st277_p152
  have hstep := st277_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p154 : ((2904975493791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT277 (i+1))
      = (∑ i ∈ Finset.range 153, stT277 (i+1)) + stT277 154 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 153
    simpa using h
  have hprev := st277_p153
  have hstep := st277_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p155 : ((2704585356921/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT277 (i+1))
      = (∑ i ∈ Finset.range 154, stT277 (i+1)) + stT277 155 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 154
    simpa using h
  have hprev := st277_p154
  have hstep := st277_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p156 : ((2733594745881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT277 (i+1))
      = (∑ i ∈ Finset.range 155, stT277 (i+1)) + stT277 156 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 155
    simpa using h
  have hprev := st277_p155
  have hstep := st277_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p157 : ((584274322461/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT277 (i+1))
      = (∑ i ∈ Finset.range 156, stT277 (i+1)) + stT277 157 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 156
    simpa using h
  have hprev := st277_p156
  have hstep := st277_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p158 : ((2820369955299/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT277 (i+1))
      = (∑ i ∈ Finset.range 157, stT277 (i+1)) + stT277 158 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 157
    simpa using h
  have hprev := st277_p157
  have hstep := st277_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p159 : ((2669934731841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT277 (i+1))
      = (∑ i ∈ Finset.range 158, stT277 (i+1)) + stT277 159 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 158
    simpa using h
  have hprev := st277_p158
  have hstep := st277_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p160 : ((11286667444923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT277 (i+1))
      = (∑ i ∈ Finset.range 159, stT277 (i+1)) + stT277 160 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 159
    simpa using h
  have hprev := st277_p159
  have hstep := st277_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p161 : ((11692097236553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT277 (i+1))
      = (∑ i ∈ Finset.range 160, stT277 (i+1)) + stT277 161 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 160
    simpa using h
  have hprev := st277_p160
  have hstep := st277_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p162 : ((2741797567357/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT277 (i+1))
      = (∑ i ∈ Finset.range 161, stT277 (i+1)) + stT277 162 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 161
    simpa using h
  have hprev := st277_p161
  have hstep := st277_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p163 : ((2691034421947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT277 (i+1))
      = (∑ i ∈ Finset.range 162, stT277 (i+1)) + stT277 163 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 162
    simpa using h
  have hprev := st277_p162
  have hstep := st277_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p164 : ((115374578177/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT277 (i+1))
      = (∑ i ∈ Finset.range 163, stT277 (i+1)) + stT277 164 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 163
    simpa using h
  have hprev := st277_p163
  have hstep := st277_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p165 : ((5778714313447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT277 (i+1))
      = (∑ i ∈ Finset.range 164, stT277 (i+1)) + stT277 165 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 164
    simpa using h
  have hprev := st277_p164
  have hstep := st277_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p166 : ((2695887937331/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT277 (i+1))
      = (∑ i ∈ Finset.range 165, stT277 (i+1)) + stT277 166 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 165
    simpa using h
  have hprev := st277_p165
  have hstep := st277_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p167 : ((10914512780021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT277 (i+1))
      = (∑ i ∈ Finset.range 166, stT277 (i+1)) + stT277 167 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 166
    simpa using h
  have hprev := st277_p166
  have hstep := st277_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p168 : ((11661423591749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT277 (i+1))
      = (∑ i ∈ Finset.range 167, stT277 (i+1)) + stT277 168 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 167
    simpa using h
  have hprev := st277_p167
  have hstep := st277_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p169 : ((11414908133179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT277 (i+1))
      = (∑ i ∈ Finset.range 168, stT277 (i+1)) + stT277 169 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 168
    simpa using h
  have hprev := st277_p168
  have hstep := st277_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p170 : ((10705378074169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT277 (i+1))
      = (∑ i ∈ Finset.range 169, stT277 (i+1)) + stT277 170 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 169
    simpa using h
  have hprev := st277_p169
  have hstep := st277_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p171 : ((11033434877979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT277 (i+1))
      = (∑ i ∈ Finset.range 170, stT277 (i+1)) + stT277 171 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 170
    simpa using h
  have hprev := st277_p170
  have hstep := st277_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p172 : ((11706958548927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT277 (i+1))
      = (∑ i ∈ Finset.range 171, stT277 (i+1)) + stT277 172 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 171
    simpa using h
  have hprev := st277_p171
  have hstep := st277_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p173 : ((2265461642851/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT277 (i+1))
      = (∑ i ∈ Finset.range 172, stT277 (i+1)) + stT277 173 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 172
    simpa using h
  have hprev := st277_p172
  have hstep := st277_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p174 : ((10680395045991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT277 (i+1))
      = (∑ i ∈ Finset.range 173, stT277 (i+1)) + stT277 174 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 173
    simpa using h
  have hprev := st277_p173
  have hstep := st277_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p175 : ((11085188442567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT277 (i+1))
      = (∑ i ∈ Finset.range 174, stT277 (i+1)) + stT277 175 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 174
    simpa using h
  have hprev := st277_p174
  have hstep := st277_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p176 : ((2343731337953/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT277 (i+1))
      = (∑ i ∈ Finset.range 175, stT277 (i+1)) + stT277 176 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 175
    simpa using h
  have hprev := st277_p175
  have hstep := st277_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p177 : ((5656082620259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT277 (i+1))
      = (∑ i ∈ Finset.range 176, stT277 (i+1)) + stT277 177 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 176
    simpa using h
  have hprev := st277_p176
  have hstep := st277_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p178 : ((5338759628441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT277 (i+1))
      = (∑ i ∈ Finset.range 177, stT277 (i+1)) + stT277 178 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 177
    simpa using h
  have hprev := st277_p177
  have hstep := st277_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p179 : ((11063133679777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT277 (i+1))
      = (∑ i ∈ Finset.range 178, stT277 (i+1)) + stT277 179 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 178
    simpa using h
  have hprev := st277_p178
  have hstep := st277_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p180 : ((1463994253369/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT277 (i+1))
      = (∑ i ∈ Finset.range 179, stT277 (i+1)) + stT277 180 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 179
    simpa using h
  have hprev := st277_p179
  have hstep := st277_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p181 : ((5684884627081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT277 (i+1))
      = (∑ i ∈ Finset.range 180, stT277 (i+1)) + stT277 181 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 180
    simpa using h
  have hprev := st277_p180
  have hstep := st277_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p182 : ((2674278076353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT277 (i+1))
      = (∑ i ∈ Finset.range 181, stT277 (i+1)) + stT277 182 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 181
    simpa using h
  have hprev := st277_p181
  have hstep := st277_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p183 : ((2742942836601/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT277 (i+1))
      = (∑ i ∈ Finset.range 182, stT277 (i+1)) + stT277 183 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 182
    simpa using h
  have hprev := st277_p182
  have hstep := st277_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p184 : ((5835820355277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT277 (i+1))
      = (∑ i ∈ Finset.range 183, stT277 (i+1)) + stT277 184 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 183
    simpa using h
  have hprev := st277_p183
  have hstep := st277_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p185 : ((11489674262839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT277 (i+1))
      = (∑ i ∈ Finset.range 184, stT277 (i+1)) + stT277 185 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 184
    simpa using h
  have hprev := st277_p184
  have hstep := st277_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p186 : ((10767284289751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT277 (i+1))
      = (∑ i ∈ Finset.range 185, stT277 (i+1)) + stT277 186 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 185
    simpa using h
  have hprev := st277_p185
  have hstep := st277_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p187 : ((2166154957467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT277 (i+1))
      = (∑ i ∈ Finset.range 186, stT277 (i+1)) + stT277 187 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 186
    simpa using h
  have hprev := st277_p186
  have hstep := st277_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p188 : ((11560047005331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT277 (i+1))
      = (∑ i ∈ Finset.range 187, stT277 (i+1)) + stT277 188 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 187
    simpa using h
  have hprev := st277_p187
  have hstep := st277_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p189 : ((11638253283603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT277 (i+1))
      = (∑ i ∈ Finset.range 188, stT277 (i+1)) + stT277 189 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 188
    simpa using h
  have hprev := st277_p188
  have hstep := st277_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p190 : ((10929729230139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT277 (i+1))
      = (∑ i ∈ Finset.range 189, stT277 (i+1)) + stT277 190 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 189
    simpa using h
  have hprev := st277_p189
  have hstep := st277_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p191 : ((10692791702089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT277 (i+1))
      = (∑ i ∈ Finset.range 190, stT277 (i+1)) + stT277 191 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 190
    simpa using h
  have hprev := st277_p190
  have hstep := st277_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p192 : ((11340101639869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT277 (i+1))
      = (∑ i ∈ Finset.range 191, stT277 (i+1)) + stT277 192 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 191
    simpa using h
  have hprev := st277_p191
  have hstep := st277_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p193 : ((5870187822627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT277 (i+1))
      = (∑ i ∈ Finset.range 192, stT277 (i+1)) + stT277 193 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 192
    simpa using h
  have hprev := st277_p192
  have hstep := st277_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p194 : ((11204847873277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT277 (i+1))
      = (∑ i ∈ Finset.range 193, stT277 (i+1)) + stT277 194 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 193
    simpa using h
  have hprev := st277_p193
  have hstep := st277_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p195 : ((10654883011117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT277 (i+1))
      = (∑ i ∈ Finset.range 194, stT277 (i+1)) + stT277 195 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 194
    simpa using h
  have hprev := st277_p194
  have hstep := st277_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p196 : ((5511433107281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT277 (i+1))
      = (∑ i ∈ Finset.range 195, stT277 (i+1)) + stT277 196 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 195
    simpa using h
  have hprev := st277_p195
  have hstep := st277_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p197 : ((5842217253941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT277 (i+1))
      = (∑ i ∈ Finset.range 196, stT277 (i+1)) + stT277 197 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 196
    simpa using h
  have hprev := st277_p196
  have hstep := st277_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p198 : ((720933489667/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT277 (i+1))
      = (∑ i ∈ Finset.range 197, stT277 (i+1)) + stT277 198 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 197
    simpa using h
  have hprev := st277_p197
  have hstep := st277_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p199 : ((1082649263263/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT277 (i+1))
      = (∑ i ∈ Finset.range 198, stT277 (i+1)) + stT277 199 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 198
    simpa using h
  have hprev := st277_p198
  have hstep := st277_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p200 : ((10723750692637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT277 (i+1))
      = (∑ i ∈ Finset.range 199, stT277 (i+1)) + stT277 200 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 199
    simpa using h
  have hprev := st277_p199
  have hstep := st277_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p201 : ((11389851707527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT277 (i+1))
      = (∑ i ∈ Finset.range 200, stT277 (i+1)) + stT277 201 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 200
    simpa using h
  have hprev := st277_p200
  have hstep := st277_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p202 : ((1468273814871/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT277 (i+1))
      = (∑ i ∈ Finset.range 201, stT277 (i+1)) + stT277 202 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 201
    simpa using h
  have hprev := st277_p201
  have hstep := st277_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p203 : ((11225027061359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT277 (i+1))
      = (∑ i ∈ Finset.range 202, stT277 (i+1)) + stT277 203 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 202
    simpa using h
  have hprev := st277_p202
  have hstep := st277_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p204 : ((2131618417491/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT277 (i+1))
      = (∑ i ∈ Finset.range 203, stT277 (i+1)) + stT277 204 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 203
    simpa using h
  have hprev := st277_p203
  have hstep := st277_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p205 : ((2187406910601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT277 (i+1))
      = (∑ i ∈ Finset.range 204, stT277 (i+1)) + stT277 205 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 204
    simpa using h
  have hprev := st277_p204
  have hstep := st277_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p206 : ((11621450707031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT277 (i+1))
      = (∑ i ∈ Finset.range 205, stT277 (i+1)) + stT277 206 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 205
    simpa using h
  have hprev := st277_p205
  have hstep := st277_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p207 : ((2330030264819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT277 (i+1))
      = (∑ i ∈ Finset.range 206, stT277 (i+1)) + stT277 207 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 206
    simpa using h
  have hprev := st277_p206
  have hstep := st277_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p208 : ((10983210977471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT277 (i+1))
      = (∑ i ∈ Finset.range 207, stT277 (i+1)) + stT277 208 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 207
    simpa using h
  have hprev := st277_p207
  have hstep := st277_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p209 : ((10639804915431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT277 (i+1))
      = (∑ i ∈ Finset.range 208, stT277 (i+1)) + stT277 209 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 208
    simpa using h
  have hprev := st277_p208
  have hstep := st277_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p210 : ((11136113464731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT277 (i+1))
      = (∑ i ∈ Finset.range 209, stT277 (i+1)) + stT277 210 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 209
    simpa using h
  have hprev := st277_p209
  have hstep := st277_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p211 : ((11723745967539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT277 (i+1))
      = (∑ i ∈ Finset.range 210, stT277 (i+1)) + stT277 211 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 210
    simpa using h
  have hprev := st277_p210
  have hstep := st277_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p212 : ((576472710323/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT277 (i+1))
      = (∑ i ∈ Finset.range 211, stT277 (i+1)) + stT277 212 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 211
    simpa using h
  have hprev := st277_p211
  have hstep := st277_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p213 : ((271109028323/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT277 (i+1))
      = (∑ i ∈ Finset.range 212, stT277 (i+1)) + stT277 213 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 212
    simpa using h
  have hprev := st277_p212
  have hstep := st277_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p214 : ((5336324557411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT277 (i+1))
      = (∑ i ∈ Finset.range 213, stT277 (i+1)) + stT277 214 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 213
    simpa using h
  have hprev := st277_p213
  have hstep := st277_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p215 : ((1407488671783/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT277 (i+1))
      = (∑ i ∈ Finset.range 214, stT277 (i+1)) + stT277 215 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 214
    simpa using h
  have hprev := st277_p214
  have hstep := st277_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p216 : ((734796684179/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT277 (i+1))
      = (∑ i ∈ Finset.range 215, stT277 (i+1)) + stT277 216 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 215
    simpa using h
  have hprev := st277_p215
  have hstep := st277_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p217 : ((11454886977249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT277 (i+1))
      = (∑ i ∈ Finset.range 216, stT277 (i+1)) + stT277 217 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 216
    simpa using h
  have hprev := st277_p216
  have hstep := st277_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p218 : ((10786601430903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT277 (i+1))
      = (∑ i ∈ Finset.range 217, stT277 (i+1)) + stT277 218 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 217
    simpa using h
  have hprev := st277_p217
  have hstep := st277_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p219 : ((10692582624273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT277 (i+1))
      = (∑ i ∈ Finset.range 218, stT277 (i+1)) + stT277 219 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 218
    simpa using h
  have hprev := st277_p218
  have hstep := st277_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p220 : ((11300104691571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT277 (i+1))
      = (∑ i ∈ Finset.range 219, stT277 (i+1)) + stT277 220 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 219
    simpa using h
  have hprev := st277_p219
  have hstep := st277_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p221 : ((2352982459767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT277 (i+1))
      = (∑ i ∈ Finset.range 220, stT277 (i+1)) + stT277 221 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 220
    simpa using h
  have hprev := st277_p220
  have hstep := st277_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p222 : ((11450424236403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT277 (i+1))
      = (∑ i ∈ Finset.range 221, stT277 (i+1)) + stT277 222 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 221
    simpa using h
  have hprev := st277_p221
  have hstep := st277_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p223 : ((10789484373953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT277 (i+1))
      = (∑ i ∈ Finset.range 222, stT277 (i+1)) + stT277 223 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 222
    simpa using h
  have hprev := st277_p222
  have hstep := st277_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p224 : ((10676647194587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT277 (i+1))
      = (∑ i ∈ Finset.range 223, stT277 (i+1)) + stT277 224 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 223
    simpa using h
  have hprev := st277_p223
  have hstep := st277_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p225 : ((11259555945011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT277 (i+1))
      = (∑ i ∈ Finset.range 224, stT277 (i+1)) + stT277 225 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 224
    simpa using h
  have hprev := st277_p224
  have hstep := st277_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p226 : ((11758825607741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT277 (i+1))
      = (∑ i ∈ Finset.range 225, stT277 (i+1)) + stT277 226 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 225
    simpa using h
  have hprev := st277_p225
  have hstep := st277_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p227 : ((11516322097309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT277 (i+1))
      = (∑ i ∈ Finset.range 226, stT277 (i+1)) + stT277 227 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 226
    simpa using h
  have hprev := st277_p226
  have hstep := st277_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p228 : ((2713541092841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT277 (i+1))
      = (∑ i ∈ Finset.range 227, stT277 (i+1)) + stT277 228 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 227
    simpa using h
  have hprev := st277_p227
  have hstep := st277_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p229 : ((5317571921821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT277 (i+1))
      = (∑ i ∈ Finset.range 228, stT277 (i+1)) + stT277 229 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 228
    simpa using h
  have hprev := st277_p228
  have hstep := st277_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p230 : ((5569376285911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT277 (i+1))
      = (∑ i ∈ Finset.range 229, stT277 (i+1)) + stT277 230 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 229
    simpa using h
  have hprev := st277_p229
  have hstep := st277_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p231 : ((2929020550997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT277 (i+1))
      = (∑ i ∈ Finset.range 230, stT277 (i+1)) + stT277 231 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 230
    simpa using h
  have hprev := st277_p230
  have hstep := st277_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p232 : ((11633628881051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT277 (i+1))
      = (∑ i ∈ Finset.range 231, stT277 (i+1)) + stT277 232 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 231
    simpa using h
  have hprev := st277_p231
  have hstep := st277_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p233 : ((10999415099681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT277 (i+1))
      = (∑ i ∈ Finset.range 232, stT277 (i+1)) + stT277 233 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 232
    simpa using h
  have hprev := st277_p232
  have hstep := st277_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p234 : ((10610027493473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT277 (i+1))
      = (∑ i ∈ Finset.range 233, stT277 (i+1)) + stT277 234 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 233
    simpa using h
  have hprev := st277_p233
  have hstep := st277_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p235 : ((10947185177257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT277 (i+1))
      = (∑ i ∈ Finset.range 234, stT277 (i+1)) + stT277 235 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 234
    simpa using h
  have hprev := st277_p234
  have hstep := st277_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p236 : ((11590917368681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT277 (i+1))
      = (∑ i ∈ Finset.range 235, stT277 (i+1)) + stT277 236 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 235
    simpa using h
  have hprev := st277_p235
  have hstep := st277_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p237 : ((5876078316853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT277 (i+1))
      = (∑ i ∈ Finset.range 236, stT277 (i+1)) + stT277 237 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 236
    simpa using h
  have hprev := st277_p236
  have hstep := st277_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p238 : ((5619110156929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT277 (i+1))
      = (∑ i ∈ Finset.range 237, stT277 (i+1)) + stT277 238 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 237
    simpa using h
  have hprev := st277_p237
  have hstep := st277_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p239 : ((333512862491/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT277 (i+1))
      = (∑ i ∈ Finset.range 238, stT277 (i+1)) + stT277 239 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 238
    simpa using h
  have hprev := st277_p238
  have hstep := st277_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p240 : ((10731575918241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT277 (i+1))
      = (∑ i ∈ Finset.range 239, stT277 (i+1)) + stT277 240 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 239
    simpa using h
  have hprev := st277_p239
  have hstep := st277_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p241 : ((11341525946329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT277 (i+1))
      = (∑ i ∈ Finset.range 240, stT277 (i+1)) + stT277 241 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 240
    simpa using h
  have hprev := st277_p240
  have hstep := st277_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p242 : ((11780132475417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT277 (i+1))
      = (∑ i ∈ Finset.range 241, stT277 (i+1)) + stT277 242 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 241
    simpa using h
  have hprev := st277_p241
  have hstep := st277_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p243 : ((11535452446999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT277 (i+1))
      = (∑ i ∈ Finset.range 242, stT277 (i+1)) + stT277 243 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 242
    simpa using h
  have hprev := st277_p242
  have hstep := st277_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p244 : ((2723949540091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT277 (i+1))
      = (∑ i ∈ Finset.range 243, stT277 (i+1)) + stT277 244 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 243
    simpa using h
  have hprev := st277_p243
  have hstep := st277_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p245 : ((2120169946481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT277 (i+1))
      = (∑ i ∈ Finset.range 244, stT277 (i+1)) + stT277 245 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 244
    simpa using h
  have hprev := st277_p244
  have hstep := st277_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p246 : ((10985908656997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT277 (i+1))
      = (∑ i ∈ Finset.range 245, stT277 (i+1)) + stT277 246 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 245
    simpa using h
  have hprev := st277_p245
  have hstep := st277_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p247 : ((11609295180317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT277 (i+1))
      = (∑ i ∈ Finset.range 246, stT277 (i+1)) + stT277 247 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 246
    simpa using h
  have hprev := st277_p246
  have hstep := st277_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p248 : ((11766467840317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT277 (i+1))
      = (∑ i ∈ Finset.range 247, stT277 (i+1)) + stT277 248 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 247
    simpa using h
  have hprev := st277_p247
  have hstep := st277_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p249 : ((11284313383467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT277 (i+1))
      = (∑ i ∈ Finset.range 248, stT277 (i+1)) + stT277 249 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 248
    simpa using h
  have hprev := st277_p248
  have hstep := st277_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p250 : ((10702730246739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT277 (i+1))
      = (∑ i ∈ Finset.range 249, stT277 (i+1)) + stT277 250 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 249
    simpa using h
  have hprev := st277_p249
  have hstep := st277_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p251 : ((2666045949821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT277 (i+1))
      = (∑ i ∈ Finset.range 250, stT277 (i+1)) + stT277 251 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 250
    simpa using h
  have hprev := st277_p250
  have hstep := st277_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p252 : ((2801879597051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT277 (i+1))
      = (∑ i ∈ Finset.range 251, stT277 (i+1)) + stT277 252 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 251
    simpa using h
  have hprev := st277_p251
  have hstep := st277_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p253 : ((586897501539/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT277 (i+1))
      = (∑ i ∈ Finset.range 252, stT277 (i+1)) + stT277 253 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 252
    simpa using h
  have hprev := st277_p252
  have hstep := st277_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p254 : ((2920619788911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT277 (i+1))
      = (∑ i ∈ Finset.range 253, stT277 (i+1)) + stT277 254 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 253
    simpa using h
  have hprev := st277_p253
  have hstep := st277_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p255 : ((5552090829897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT277 (i+1))
      = (∑ i ∈ Finset.range 254, stT277 (i+1)) + stT277 255 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 254
    simpa using h
  have hprev := st277_p254
  have hstep := st277_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p256 : ((10622216513651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT277 (i+1))
      = (∑ i ∈ Finset.range 255, stT277 (i+1)) + stT277 256 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 255
    simpa using h
  have hprev := st277_p255
  have hstep := st277_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p257 : ((10745718488049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT277 (i+1))
      = (∑ i ∈ Finset.range 256, stT277 (i+1)) + stT277 257 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 256
    simpa using h
  have hprev := st277_p256
  have hstep := st277_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p258 : ((11341236621789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT277 (i+1))
      = (∑ i ∈ Finset.range 257, stT277 (i+1)) + stT277 258 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 257
    simpa using h
  have hprev := st277_p257
  have hstep := st277_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p259 : ((11784748687443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT277 (i+1))
      = (∑ i ∈ Finset.range 258, stT277 (i+1)) + stT277 259 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 258
    simpa using h
  have hprev := st277_p258
  have hstep := st277_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p260 : ((11617794745773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT277 (i+1))
      = (∑ i ∈ Finset.range 259, stT277 (i+1)) + stT277 260 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 259
    simpa using h
  have hprev := st277_p259
  have hstep := st277_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p261 : ((11015782314473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT277 (i+1))
      = (∑ i ∈ Finset.range 260, stT277 (i+1)) + stT277 261 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 260
    simpa using h
  have hprev := st277_p260
  have hstep := st277_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p262 : ((10596238475203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT277 (i+1))
      = (∑ i ∈ Finset.range 261, stT277 (i+1)) + stT277 262 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 261
    simpa using h
  have hprev := st277_p261
  have hstep := st277_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p263 : ((10783596585547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT277 (i+1))
      = (∑ i ∈ Finset.range 262, stT277 (i+1)) + stT277 263 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 262
    simpa using h
  have hprev := st277_p262
  have hstep := st277_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p264 : ((1138540213383/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT277 (i+1))
      = (∑ i ∈ Finset.range 263, stT277 (i+1)) + stT277 264 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 263
    simpa using h
  have hprev := st277_p263
  have hstep := st277_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p265 : ((471879953079/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT277 (i+1))
      = (∑ i ∈ Finset.range 264, stT277 (i+1)) + stT277 265 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 264
    simpa using h
  have hprev := st277_p264
  have hstep := st277_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p266 : ((2322101478171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT277 (i+1))
      = (∑ i ∈ Finset.range 265, stT277 (i+1)) + stT277 266 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 265
    simpa using h
  have hprev := st277_p265
  have hstep := st277_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p267 : ((5506779870813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT277 (i+1))
      = (∑ i ∈ Finset.range 266, stT277 (i+1)) + stT277 267 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 266
    simpa using h
  have hprev := st277_p266
  have hstep := st277_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p268 : ((5296862566461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT277 (i+1))
      = (∑ i ∈ Finset.range 267, stT277 (i+1)) + stT277 268 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 267
    simpa using h
  have hprev := st277_p267
  have hstep := st277_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p269 : ((5379325843961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT277 (i+1))
      = (∑ i ∈ Finset.range 268, stT277 (i+1)) + stT277 269 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 268
    simpa using h
  have hprev := st277_p268
  have hstep := st277_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p270 : ((5672657752481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT277 (i+1))
      = (∑ i ∈ Finset.range 269, stT277 (i+1)) + stT277 270 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 269
    simpa using h
  have hprev := st277_p269
  have hstep := st277_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p271 : ((5893829444801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT277 (i+1))
      = (∑ i ∈ Finset.range 270, stT277 (i+1)) + stT277 271 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 270
    simpa using h
  have hprev := st277_p270
  have hstep := st277_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p272 : ((5832248644891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT277 (i+1))
      = (∑ i ∈ Finset.range 271, stT277 (i+1)) + stT277 272 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 271
    simpa using h
  have hprev := st277_p271
  have hstep := st277_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p273 : ((5547944910189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT277 (i+1))
      = (∑ i ∈ Finset.range 272, stT277 (i+1)) + stT277 273 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 272
    simpa using h
  have hprev := st277_p272
  have hstep := st277_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p274 : ((2123946310023/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT277 (i+1))
      = (∑ i ∈ Finset.range 273, stT277 (i+1)) + stT277 274 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 273
    simpa using h
  have hprev := st277_p273
  have hstep := st277_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p275 : ((10680692853161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT277 (i+1))
      = (∑ i ∈ Finset.range 274, stT277 (i+1)) + stT277 275 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 274
    simpa using h
  have hprev := st277_p274
  have hstep := st277_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p276 : ((11218942580393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT277 (i+1))
      = (∑ i ∈ Finset.range 275, stT277 (i+1)) + stT277 276 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 275
    simpa using h
  have hprev := st277_p275
  have hstep := st277_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p277 : ((11734937621101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT277 (i+1))
      = (∑ i ∈ Finset.range 276, stT277 (i+1)) + stT277 277 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 276
    simpa using h
  have hprev := st277_p276
  have hstep := st277_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p278 : ((11755774483021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT277 (i+1))
      = (∑ i ∈ Finset.range 277, stT277 (i+1)) + stT277 278 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 277
    simpa using h
  have hprev := st277_p277
  have hstep := st277_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p279 : ((2816344158099/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT277 (i+1))
      = (∑ i ∈ Finset.range 278, stT277 (i+1)) + stT277 279 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 278
    simpa using h
  have hprev := st277_p278
  have hstep := st277_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p280 : ((10710380546121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT277 (i+1))
      = (∑ i ∈ Finset.range 279, stT277 (i+1)) + stT277 280 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 279
    simpa using h
  have hprev := st277_p279
  have hstep := st277_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p281 : ((10589957383821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT277 (i+1))
      = (∑ i ∈ Finset.range 280, stT277 (i+1)) + stT277 281 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 280
    simpa using h
  have hprev := st277_p280
  have hstep := st277_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p282 : ((11009063949621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT277 (i+1))
      = (∑ i ∈ Finset.range 281, stT277 (i+1)) + stT277 282 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 281
    simpa using h
  have hprev := st277_p281
  have hstep := st277_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p283 : ((11592715277673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT277 (i+1))
      = (∑ i ∈ Finset.range 282, stT277 (i+1)) + stT277 283 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 282
    simpa using h
  have hprev := st277_p282
  have hstep := st277_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p284 : ((11825496834163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT277 (i+1))
      = (∑ i ∈ Finset.range 283, stT277 (i+1)) + stT277 284 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 283
    simpa using h
  have hprev := st277_p283
  have hstep := st277_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p285 : ((460223665941/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT277 (i+1))
      = (∑ i ∈ Finset.range 284, stT277 (i+1)) + stT277 285 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 284
    simpa using h
  have hprev := st277_p284
  have hstep := st277_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p286 : ((682157309229/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT277 (i+1))
      = (∑ i ∈ Finset.range 285, stT277 (i+1)) + stT277 286 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 285
    simpa using h
  have hprev := st277_p285
  have hstep := st277_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p287 : ((660299757051/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT277 (i+1))
      = (∑ i ∈ Finset.range 286, stT277 (i+1)) + stT277 287 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 286
    simpa using h
  have hprev := st277_p286
  have hstep := st277_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p288 : ((5377690607243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT277 (i+1))
      = (∑ i ∈ Finset.range 287, stT277 (i+1)) + stT277 288 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 287
    simpa using h
  have hprev := st277_p287
  have hstep := st277_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p289 : ((11320474461351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT277 (i+1))
      = (∑ i ∈ Finset.range 288, stT277 (i+1)) + stT277 289 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 288
    simpa using h
  have hprev := st277_p288
  have hstep := st277_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p290 : ((11778674593491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT277 (i+1))
      = (∑ i ∈ Finset.range 289, stT277 (i+1)) + stT277 290 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 289
    simpa using h
  have hprev := st277_p289
  have hstep := st277_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p291 : ((1468060186509/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT277 (i+1))
      = (∑ i ∈ Finset.range 290, stT277 (i+1)) + stT277 291 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 290
    simpa using h
  have hprev := st277_p290
  have hstep := st277_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p292 : ((2812330284823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT277 (i+1))
      = (∑ i ∈ Finset.range 291, stT277 (i+1)) + stT277 292 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 291
    simpa using h
  have hprev := st277_p291
  have hstep := st277_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p293 : ((1338475706253/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT277 (i+1))
      = (∑ i ∈ Finset.range 292, stT277 (i+1)) + stT277 293 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 292
    simpa using h
  have hprev := st277_p292
  have hstep := st277_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p294 : ((82561582761/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT277 (i+1))
      = (∑ i ∈ Finset.range 293, stT277 (i+1)) + stT277 294 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 293
    simpa using h
  have hprev := st277_p293
  have hstep := st277_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p295 : ((547109830527/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT277 (i+1))
      = (∑ i ∈ Finset.range 294, stT277 (i+1)) + stT277 295 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 294
    simpa using h
  have hprev := st277_p294
  have hstep := st277_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p296 : ((5761089858849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT277 (i+1))
      = (∑ i ∈ Finset.range 295, stT277 (i+1)) + stT277 296 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 295
    simpa using h
  have hprev := st277_p295
  have hstep := st277_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p297 : ((739753848683/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT277 (i+1))
      = (∑ i ∈ Finset.range 296, stT277 (i+1)) + stT277 297 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 296
    simpa using h
  have hprev := st277_p296
  have hstep := st277_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p298 : ((5816125868689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT277 (i+1))
      = (∑ i ∈ Finset.range 297, stT277 (i+1)) + stT277 298 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 297
    simpa using h
  have hprev := st277_p297
  have hstep := st277_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p299 : ((11076968132253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT277 (i+1))
      = (∑ i ∈ Finset.range 298, stT277 (i+1)) + stT277 299 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 298
    simpa using h
  have hprev := st277_p298
  have hstep := st277_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p300 : ((10614376035821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT277 (i+1))
      = (∑ i ∈ Finset.range 299, stT277 (i+1)) + stT277 300 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 299
    simpa using h
  have hprev := st277_p299
  have hstep := st277_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p301 : ((5305021652337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT277 (i+1))
      = (∑ i ∈ Finset.range 300, stT277 (i+1)) + stT277 301 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 300
    simpa using h
  have hprev := st277_p300
  have hstep := st277_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p302 : ((11064776785379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT277 (i+1))
      = (∑ i ∈ Finset.range 301, stT277 (i+1)) + stT277 302 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 301
    simpa using h
  have hprev := st277_p301
  have hstep := st277_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p303 : ((11620481477903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT277 (i+1))
      = (∑ i ∈ Finset.range 302, stT277 (i+1)) + stT277 303 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 302
    simpa using h
  have hprev := st277_p302
  have hstep := st277_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p304 : ((5922404606717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT277 (i+1))
      = (∑ i ∈ Finset.range 303, stT277 (i+1)) + stT277 304 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 303
    simpa using h
  have hprev := st277_p303
  have hstep := st277_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p305 : ((5783186321451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT277 (i+1))
      = (∑ i ∈ Finset.range 304, stT277 (i+1)) + stT277 305 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 304
    simpa using h
  have hprev := st277_p304
  have hstep := st277_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p306 : ((2750412797811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT277 (i+1))
      = (∑ i ∈ Finset.range 305, stT277 (i+1)) + stT277 306 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 305
    simpa using h
  have hprev := st277_p305
  have hstep := st277_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p307 : ((10583027422247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT277 (i+1))
      = (∑ i ∈ Finset.range 306, stT277 (i+1)) + stT277 307 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 306
    simpa using h
  have hprev := st277_p306
  have hstep := st277_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p308 : ((10627079954471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT277 (i+1))
      = (∑ i ∈ Finset.range 307, stT277 (i+1)) + stT277 308 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 307
    simpa using h
  have hprev := st277_p307
  have hstep := st277_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p309 : ((11098021573671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT277 (i+1))
      = (∑ i ∈ Finset.range 308, stT277 (i+1)) + stT277 309 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 308
    simpa using h
  have hprev := st277_p308
  have hstep := st277_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p310 : ((5820333424009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT277 (i+1))
      = (∑ i ∈ Finset.range 309, stT277 (i+1)) + stT277 310 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 309
    simpa using h
  have hprev := st277_p309
  have hstep := st277_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p311 : ((11850513364261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT277 (i+1))
      = (∑ i ∈ Finset.range 310, stT277 (i+1)) + stT277 311 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 310
    simpa using h
  have hprev := st277_p310
  have hstep := st277_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p312 : ((2314813085201/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT277 (i+1))
      = (∑ i ∈ Finset.range 311, stT277 (i+1)) + stT277 312 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 311
    simpa using h
  have hprev := st277_p311
  have hstep := st277_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p313 : ((11017368155107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT277 (i+1))
      = (∑ i ∈ Finset.range 312, stT277 (i+1)) + stT277 313 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 312
    simpa using h
  have hprev := st277_p312
  have hstep := st277_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p314 : ((10589101484737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT277 (i+1))
      = (∑ i ∈ Finset.range 313, stT277 (i+1)) + stT277 314 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 313
    simpa using h
  have hprev := st277_p313
  have hstep := st277_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p315 : ((10599917202193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT277 (i+1))
      = (∑ i ∈ Finset.range 314, stT277 (i+1)) + stT277 315 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 314
    simpa using h
  have hprev := st277_p314
  have hstep := st277_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p316 : ((11039572683843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT277 (i+1))
      = (∑ i ∈ Finset.range 315, stT277 (i+1)) + stT277 316 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 315
    simpa using h
  have hprev := st277_p315
  have hstep := st277_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p317 : ((2897455819767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT277 (i+1))
      = (∑ i ∈ Finset.range 316, stT277 (i+1)) + stT277 317 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 316
    simpa using h
  have hprev := st277_p316
  have hstep := st277_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p318 : ((741065041887/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT277 (i+1))
      = (∑ i ∈ Finset.range 317, stT277 (i+1)) + stT277 318 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 317
    simpa using h
  have hprev := st277_p317
  have hstep := st277_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p319 : ((11652992705379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT277 (i+1))
      = (∑ i ∈ Finset.range 318, stT277 (i+1)) + stT277 319 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 318
    simpa using h
  have hprev := st277_p318
  have hstep := st277_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p320 : ((444970708743/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT277 (i+1))
      = (∑ i ∈ Finset.range 319, stT277 (i+1)) + stT277 320 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 319
    simpa using h
  have hprev := st277_p319
  have hstep := st277_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p321 : ((10643639267639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT277 (i+1))
      = (∑ i ∈ Finset.range 320, stT277 (i+1)) + stT277 321 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 320
    simpa using h
  have hprev := st277_p320
  have hstep := st277_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p322 : ((1318269376181/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT277 (i+1))
      = (∑ i ∈ Finset.range 321, stT277 (i+1)) + stT277 322 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 321
    simpa using h
  have hprev := st277_p321
  have hstep := st277_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p323 : ((5448676477191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT277 (i+1))
      = (∑ i ∈ Finset.range 322, stT277 (i+1)) + stT277 323 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 322
    simpa using h
  have hprev := st277_p322
  have hstep := st277_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p324 : ((11452606288017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT277 (i+1))
      = (∑ i ∈ Finset.range 323, stT277 (i+1)) + stT277 324 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 323
    simpa using h
  have hprev := st277_p323
  have hstep := st277_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p325 : ((11830110146517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT277 (i+1))
      = (∑ i ∈ Finset.range 324, stT277 (i+1)) + stT277 325 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 324
    simpa using h
  have hprev := st277_p324
  have hstep := st277_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p326 : ((11773461363099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT277 (i+1))
      = (∑ i ∈ Finset.range 325, stT277 (i+1)) + stT277 326 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 325
    simpa using h
  have hprev := st277_p325
  have hstep := st277_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p327 : ((11323353680229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT277 (i+1))
      = (∑ i ∈ Finset.range 326, stT277 (i+1)) + stT277 327 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 326
    simpa using h
  have hprev := st277_p326
  have hstep := st277_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p328 : ((10785187916107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT277 (i+1))
      = (∑ i ∈ Finset.range 327, stT277 (i+1)) + stT277 328 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 327
    simpa using h
  have hprev := st277_p327
  have hstep := st277_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p329 : ((10519997893609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT277 (i+1))
      = (∑ i ∈ Finset.range 328, stT277 (i+1)) + stT277 329 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 328
    simpa using h
  have hprev := st277_p328
  have hstep := st277_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p330 : ((2140597317141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT277 (i+1))
      = (∑ i ∈ Finset.range 329, stT277 (i+1)) + stT277 330 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 329
    simpa using h
  have hprev := st277_p329
  have hstep := st277_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p331 : ((1401318139279/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT277 (i+1))
      = (∑ i ∈ Finset.range 330, stT277 (i+1)) + stT277 331 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 330
    simpa using h
  have hprev := st277_p330
  have hstep := st277_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p332 : ((11706633746089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT277 (i+1))
      = (∑ i ∈ Finset.range 331, stT277 (i+1)) + stT277 332 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 331
    simpa using h
  have hprev := st277_p331
  have hstep := st277_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p333 : ((11866392663957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT277 (i+1))
      = (∑ i ∈ Finset.range 332, stT277 (i+1)) + stT277 333 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 332
    simpa using h
  have hprev := st277_p332
  have hstep := st277_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p334 : ((11587532076021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT277 (i+1))
      = (∑ i ∈ Finset.range 333, stT277 (i+1)) + stT277 334 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 333
    simpa using h
  have hprev := st277_p333
  have hstep := st277_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p335 : ((5526459624081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT277 (i+1))
      = (∑ i ∈ Finset.range 334, stT277 (i+1)) + stT277 335 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 334
    simpa using h
  have hprev := st277_p334
  have hstep := st277_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p336 : ((1326017733139/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT277 (i+1))
      = (∑ i ∈ Finset.range 335, stT277 (i+1)) + stT277 336 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 335
    simpa using h
  have hprev := st277_p335
  have hstep := st277_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p337 : ((5145274619/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT277 (i+1))
      = (∑ i ∈ Finset.range 336, stT277 (i+1)) + stT277 337 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 336
    simpa using h
  have hprev := st277_p336
  have hstep := st277_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p338 : ((1360505940753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT277 (i+1))
      = (∑ i ∈ Finset.range 337, stT277 (i+1)) + stT277 338 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 337
    simpa using h
  have hprev := st277_p337
  have hstep := st277_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p339 : ((1428264043253/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT277 (i+1))
      = (∑ i ∈ Finset.range 338, stT277 (i+1)) + stT277 339 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 338
    simpa using h
  have hprev := st277_p338
  have hstep := st277_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p340 : ((5910668649729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT277 (i+1))
      = (∑ i ∈ Finset.range 339, stT277 (i+1)) + stT277 340 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 339
    simpa using h
  have hprev := st277_p339
  have hstep := st277_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p341 : ((2955745481517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT277 (i+1))
      = (∑ i ∈ Finset.range 340, stT277 (i+1)) + stT277 341 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 340
    simpa using h
  have hprev := st277_p340
  have hstep := st277_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p342 : ((11432031414241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT277 (i+1))
      = (∑ i ∈ Finset.range 341, stT277 (i+1)) + stT277 342 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 341
    simpa using h
  have hprev := st277_p341
  have hstep := st277_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p343 : ((10892625683841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT277 (i+1))
      = (∑ i ∈ Finset.range 342, stT277 (i+1)) + stT277 343 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 342
    simpa using h
  have hprev := st277_p342
  have hstep := st277_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p344 : ((10537738773253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT277 (i+1))
      = (∑ i ∈ Finset.range 343, stT277 (i+1)) + stT277 344 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 343
    simpa using h
  have hprev := st277_p343
  have hstep := st277_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p345 : ((10583791883993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT277 (i+1))
      = (∑ i ∈ Finset.range 344, stT277 (i+1)) + stT277 345 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 344
    simpa using h
  have hprev := st277_p344
  have hstep := st277_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p346 : ((2750161371743/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT277 (i+1))
      = (∑ i ∈ Finset.range 345, stT277 (i+1)) + stT277 346 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 345
    simpa using h
  have hprev := st277_p345
  have hstep := st277_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p347 : ((1441729559659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT277 (i+1))
      = (∑ i ∈ Finset.range 346, stT277 (i+1)) + stT277 347 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 346
    simpa using h
  have hprev := st277_p346
  have hstep := st277_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p348 : ((1482683836017/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT277 (i+1))
      = (∑ i ∈ Finset.range 347, stT277 (i+1)) + stT277 348 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 347
    simpa using h
  have hprev := st277_p347
  have hstep := st277_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p349 : ((184190975211/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT277 (i+1))
      = (∑ i ∈ Finset.range 348, stT277 (i+1)) + stT277 349 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 348
    simpa using h
  have hprev := st277_p348
  have hstep := st277_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p350 : ((5679892027611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT277 (i+1))
      = (∑ i ∈ Finset.range 349, stT277 (i+1)) + stT277 350 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 349
    simpa using h
  have hprev := st277_p349
  have hstep := st277_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p351 : ((5415966428507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT277 (i+1))
      = (∑ i ∈ Finset.range 350, stT277 (i+1)) + stT277 351 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 350
    simpa using h
  have hprev := st277_p350
  have hstep := st277_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p352 : ((164318690719/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT277 (i+1))
      = (∑ i ∈ Finset.range 351, stT277 (i+1)) + stT277 352 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 351
    simpa using h
  have hprev := st277_p351
  have hstep := st277_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p353 : ((1324642772773/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT277 (i+1))
      = (∑ i ∈ Finset.range 352, stT277 (i+1)) + stT277 353 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 352
    simpa using h
  have hprev := st277_p352
  have hstep := st277_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p354 : ((4410022177/4000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT277 (i+1))
      = (∑ i ∈ Finset.range 353, stT277 (i+1)) + stT277 354 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 353
    simpa using h
  have hprev := st277_p353
  have hstep := st277_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p355 : ((2887521628521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT277 (i+1))
      = (∑ i ∈ Finset.range 354, stT277 (i+1)) + stT277 355 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 354
    simpa using h
  have hprev := st277_p354
  have hstep := st277_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p356 : ((5934363570831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT277 (i+1))
      = (∑ i ∈ Finset.range 355, stT277 (i+1)) + stT277 356 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 355
    simpa using h
  have hprev := st277_p355
  have hstep := st277_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p357 : ((11799090151887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT277 (i+1))
      = (∑ i ∈ Finset.range 356, stT277 (i+1)) + stT277 357 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 356
    simpa using h
  have hprev := st277_p356
  have hstep := st277_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p358 : ((2845715072039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT277 (i+1))
      = (∑ i ∈ Finset.range 357, stT277 (i+1)) + stT277 358 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 357
    simpa using h
  have hprev := st277_p357
  have hstep := st277_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p359 : ((84829398837/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT277 (i+1))
      = (∑ i ∈ Finset.range 358, stT277 (i+1)) + stT277 359 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 358
    simpa using h
  have hprev := st277_p358
  have hstep := st277_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p360 : ((657623407947/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT277 (i+1))
      = (∑ i ∈ Finset.range 359, stT277 (i+1)) + stT277 360 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 359
    simpa using h
  have hprev := st277_p359
  have hstep := st277_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p361 : ((5281139338611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT277 (i+1))
      = (∑ i ∈ Finset.range 360, stT277 (i+1)) + stT277 361 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 360
    simpa using h
  have hprev := st277_p360
  have hstep := st277_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p362 : ((1095466743597/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT277 (i+1))
      = (∑ i ∈ Finset.range 361, stT277 (i+1)) + stT277 362 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 361
    simpa using h
  have hprev := st277_p361
  have hstep := st277_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p363 : ((11479158308103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT277 (i+1))
      = (∑ i ∈ Finset.range 362, stT277 (i+1)) + stT277 363 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 362
    simpa using h
  have hprev := st277_p362
  have hstep := st277_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p364 : ((11844932375229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT277 (i+1))
      = (∑ i ∈ Finset.range 363, stT277 (i+1)) + stT277 364 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 363
    simpa using h
  have hprev := st277_p363
  have hstep := st277_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p365 : ((2962864210731/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT277 (i+1))
      = (∑ i ∈ Finset.range 364, stT277 (i+1)) + stT277 365 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 364
    simpa using h
  have hprev := st277_p364
  have hstep := st277_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p366 : ((718556980723/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT277 (i+1))
      = (∑ i ∈ Finset.range 365, stT277 (i+1)) + stT277 366 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 365
    simpa using h
  have hprev := st277_p365
  have hstep := st277_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p367 : ((1372019363759/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT277 (i+1))
      = (∑ i ∈ Finset.range 366, stT277 (i+1)) + stT277 367 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 366
    simpa using h
  have hprev := st277_p366
  have hstep := st277_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p368 : ((5286068838083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT277 (i+1))
      = (∑ i ∈ Finset.range 367, stT277 (i+1)) + stT277 368 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 367
    simpa using h
  have hprev := st277_p367
  have hstep := st277_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p369 : ((5251022871903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT277 (i+1))
      = (∑ i ∈ Finset.range 368, stT277 (i+1)) + stT277 369 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 368
    simpa using h
  have hprev := st277_p368
  have hstep := st277_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p370 : ((5400913231903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT277 (i+1))
      = (∑ i ∈ Finset.range 369, stT277 (i+1)) + stT277 370 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 369
    simpa using h
  have hprev := st277_p369
  have hstep := st277_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p371 : ((5654865117307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT277 (i+1))
      = (∑ i ∈ Finset.range 370, stT277 (i+1)) + stT277 371 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 370
    simpa using h
  have hprev := st277_p370
  have hstep := st277_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p372 : ((11755169216789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT277 (i+1))
      = (∑ i ∈ Finset.range 371, stT277 (i+1)) + stT277 372 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 371
    simpa using h
  have hprev := st277_p371
  have hstep := st277_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p373 : ((11903221676649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT277 (i+1))
      = (∑ i ∈ Finset.range 372, stT277 (i+1)) + stT277 373 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 372
    simpa using h
  have hprev := st277_p372
  have hstep := st277_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p374 : ((11677546892457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT277 (i+1))
      = (∑ i ∈ Finset.range 373, stT277 (i+1)) + stT277 374 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 373
    simpa using h
  have hprev := st277_p373
  have hstep := st277_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p375 : ((11197873569023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT277 (i+1))
      = (∑ i ∈ Finset.range 374, stT277 (i+1)) + stT277 375 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 374
    simpa using h
  have hprev := st277_p374
  have hstep := st277_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p376 : ((1071485709929/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT277 (i+1))
      = (∑ i ∈ Finset.range 375, stT277 (i+1)) + stT277 376 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 375
    simpa using h
  have hprev := st277_p375
  have hstep := st277_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p377 : ((5239197921471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT277 (i+1))
      = (∑ i ∈ Finset.range 376, stT277 (i+1)) + stT277 377 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 376
    simpa using h
  have hprev := st277_p376
  have hstep := st277_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p378 : ((5304508293903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT277 (i+1))
      = (∑ i ∈ Finset.range 377, stT277 (i+1)) + stT277 378 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 377
    simpa using h
  have hprev := st277_p377
  have hstep := st277_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p379 : ((5519028153193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT277 (i+1))
      = (∑ i ∈ Finset.range 378, stT277 (i+1)) + stT277 379 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 378
    simpa using h
  have hprev := st277_p378
  have hstep := st277_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p380 : ((2886357019209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT277 (i+1))
      = (∑ i ∈ Finset.range 379, stT277 (i+1)) + stT277 380 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 379
    simpa using h
  have hprev := st277_p379
  have hstep := st277_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p381 : ((2968373527559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT277 (i+1))
      = (∑ i ∈ Finset.range 380, stT277 (i+1)) + stT277 381 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 380
    simpa using h
  have hprev := st277_p380
  have hstep := st277_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p382 : ((11857575299351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT277 (i+1))
      = (∑ i ∈ Finset.range 381, stT277 (i+1)) + stT277 382 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 381
    simpa using h
  have hprev := st277_p381
  have hstep := st277_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p383 : ((11507297499989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT277 (i+1))
      = (∑ i ∈ Finset.range 382, stT277 (i+1)) + stT277 383 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 382
    simpa using h
  have hprev := st277_p382
  have hstep := st277_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p384 : ((2199835759209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT277 (i+1))
      = (∑ i ∈ Finset.range 383, stT277 (i+1)) + stT277 384 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 383
    simpa using h
  have hprev := st277_p383
  have hstep := st277_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p385 : ((10586492347341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT277 (i+1))
      = (∑ i ∈ Finset.range 384, stT277 (i+1)) + stT277 385 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 384
    simpa using h
  have hprev := st277_p384
  have hstep := st277_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p386 : ((10472859981617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT277 (i+1))
      = (∑ i ∈ Finset.range 385, stT277 (i+1)) + stT277 386 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 385
    simpa using h
  have hprev := st277_p385
  have hstep := st277_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p387 : ((10712776564433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT277 (i+1))
      = (∑ i ∈ Finset.range 386, stT277 (i+1)) + stT277 387 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 386
    simpa using h
  have hprev := st277_p386
  have hstep := st277_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p388 : ((11187096463679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT277 (i+1))
      = (∑ i ∈ Finset.range 387, stT277 (i+1)) + stT277 388 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 387
    simpa using h
  have hprev := st277_p387
  have hstep := st277_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p389 : ((11663587775439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT277 (i+1))
      = (∑ i ∈ Finset.range 388, stT277 (i+1)) + stT277 389 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 388
    simpa using h
  have hprev := st277_p388
  have hstep := st277_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p390 : ((595559832319/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT277 (i+1))
      = (∑ i ∈ Finset.range 389, stT277 (i+1)) + stT277 390 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 389
    simpa using h
  have hprev := st277_p389
  have hstep := st277_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p391 : ((1476439475731/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT277 (i+1))
      = (∑ i ∈ Finset.range 390, stT277 (i+1)) + stT277 391 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 390
    simpa using h
  have hprev := st277_p390
  have hstep := st277_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p392 : ((2853501516173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT277 (i+1))
      = (∑ i ∈ Finset.range 391, stT277 (i+1)) + stT277 392 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 391
    simpa using h
  have hprev := st277_p391
  have hstep := st277_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p393 : ((2727491885237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT277 (i+1))
      = (∑ i ∈ Finset.range 392, stT277 (i+1)) + stT277 393 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 392
    simpa using h
  have hprev := st277_p392
  have hstep := st277_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p394 : ((10539535097357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT277 (i+1))
      = (∑ i ∈ Finset.range 393, stT277 (i+1)) + stT277 394 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 393
    simpa using h
  have hprev := st277_p393
  have hstep := st277_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p395 : ((10477340107807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT277 (i+1))
      = (∑ i ∈ Finset.range 394, stT277 (i+1)) + stT277 395 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 394
    simpa using h
  have hprev := st277_p394
  have hstep := st277_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p396 : ((10751241563851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT277 (i+1))
      = (∑ i ∈ Finset.range 395, stT277 (i+1)) + stT277 396 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 395
    simpa using h
  have hprev := st277_p395
  have hstep := st277_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p397 : ((701957572891/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT277 (i+1))
      = (∑ i ∈ Finset.range 396, stT277 (i+1)) + stT277 397 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 396
    simpa using h
  have hprev := st277_p396
  have hstep := st277_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p398 : ((584637426547/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT277 (i+1))
      = (∑ i ∈ Finset.range 397, stT277 (i+1)) + stT277 398 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 397
    simpa using h
  have hprev := st277_p397
  have hstep := st277_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p399 : ((2980364128821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT277 (i+1))
      = (∑ i ∈ Finset.range 398, stT277 (i+1)) + stT277 399 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 398
    simpa using h
  have hprev := st277_p398
  have hstep := st277_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p400 : ((11812873798119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT277 (i+1))
      = (∑ i ∈ Finset.range 399, stT277 (i+1)) + stT277 400 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 399
    simpa using h
  have hprev := st277_p399
  have hstep := st277_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p401 : ((11418435880899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT277 (i+1))
      = (∑ i ∈ Finset.range 400, stT277 (i+1)) + stT277 401 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 400
    simpa using h
  have hprev := st277_p400
  have hstep := st277_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p402 : ((10919874397839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT277 (i+1))
      = (∑ i ∈ Finset.range 401, stT277 (i+1)) + stT277 402 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 401
    simpa using h
  have hprev := st277_p401
  have hstep := st277_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p403 : ((10544628050903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT277 (i+1))
      = (∑ i ∈ Finset.range 402, stT277 (i+1)) + stT277 403 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 402
    simpa using h
  have hprev := st277_p402
  have hstep := st277_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p404 : ((5231073929263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT277 (i+1))
      = (∑ i ∈ Finset.range 403, stT277 (i+1)) + stT277 404 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 403
    simpa using h
  have hprev := st277_p403
  have hstep := st277_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p405 : ((5354144876691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT277 (i+1))
      = (∑ i ∈ Finset.range 404, stT277 (i+1)) + stT277 405 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 404
    simpa using h
  have hprev := st277_p404
  have hstep := st277_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p406 : ((111710801183/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT277 (i+1))
      = (∑ i ∈ Finset.range 405, stT277 (i+1)) + stT277 406 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 405
    simpa using h
  have hprev := st277_p405
  have hstep := st277_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p407 : ((5821400445061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT277 (i+1))
      = (∑ i ∈ Finset.range 406, stT277 (i+1)) + stT277 407 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 406
    simpa using h
  have hprev := st277_p406
  have hstep := st277_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p408 : ((11913676616561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT277 (i+1))
      = (∑ i ∈ Finset.range 407, stT277 (i+1)) + stT277 408 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 407
    simpa using h
  have hprev := st277_p407
  have hstep := st277_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p409 : ((2966183889587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT277 (i+1))
      = (∑ i ∈ Finset.range 408, stT277 (i+1)) + stT277 409 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 408
    simpa using h
  have hprev := st277_p408
  have hstep := st277_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p410 : ((44995941083/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT277 (i+1))
      = (∑ i ∈ Finset.range 409, stT277 (i+1)) + stT277 410 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 409
    simpa using h
  have hprev := st277_p409
  have hstep := st277_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p411 : ((68932796447/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT277 (i+1))
      = (∑ i ∈ Finset.range 410, stT277 (i+1)) + stT277 411 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 410
    simpa using h
  have hprev := st277_p410
  have hstep := st277_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p412 : ((2121980265897/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT277 (i+1))
      = (∑ i ∈ Finset.range 411, stT277 (i+1)) + stT277 412 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 411
    simpa using h
  have hprev := st277_p411
  have hstep := st277_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p413 : ((10442706956513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT277 (i+1))
      = (∑ i ∈ Finset.range 412, stT277 (i+1)) + stT277 413 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 412
    simpa using h
  have hprev := st277_p412
  have hstep := st277_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p414 : ((5299403568177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT277 (i+1))
      = (∑ i ∈ Finset.range 413, stT277 (i+1)) + stT277 414 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 413
    simpa using h
  have hprev := st277_p413
  have hstep := st277_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p415 : ((5504795123377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT277 (i+1))
      = (∑ i ∈ Finset.range 414, stT277 (i+1)) + stT277 415 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 414
    simpa using h
  have hprev := st277_p414
  have hstep := st277_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p416 : ((5748991902517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT277 (i+1))
      = (∑ i ∈ Finset.range 415, stT277 (i+1)) + stT277 416 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 415
    simpa using h
  have hprev := st277_p415
  have hstep := st277_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p417 : ((5927717462053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT277 (i+1))
      = (∑ i ∈ Finset.range 416, stT277 (i+1)) + stT277 417 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 416
    simpa using h
  have hprev := st277_p416
  have hstep := st277_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p418 : ((5965419424483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT277 (i+1))
      = (∑ i ∈ Finset.range 417, stT277 (i+1)) + stT277 418 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 417
    simpa using h
  have hprev := st277_p417
  have hstep := st277_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p419 : ((5846789443189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT277 (i+1))
      = (∑ i ∈ Finset.range 418, stT277 (i+1)) + stT277 419 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 418
    simpa using h
  have hprev := st277_p418
  have hstep := st277_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p420 : ((5622387609603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT277 (i+1))
      = (∑ i ∈ Finset.range 419, stT277 (i+1)) + stT277 420 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 419
    simpa using h
  have hprev := st277_p419
  have hstep := st277_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p421 : ((10773177981621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT277 (i+1))
      = (∑ i ∈ Finset.range 420, stT277 (i+1)) + stT277 421 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 420
    simpa using h
  have hprev := st277_p420
  have hstep := st277_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p422 : ((10475345367603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT277 (i+1))
      = (∑ i ∈ Finset.range 421, stT277 (i+1)) + stT277 422 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 421
    simpa using h
  have hprev := st277_p421
  have hstep := st277_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p423 : ((10474008270853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT277 (i+1))
      = (∑ i ∈ Finset.range 422, stT277 (i+1)) + stT277 423 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 422
    simpa using h
  have hprev := st277_p422
  have hstep := st277_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p424 : ((10768420963081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT277 (i+1))
      = (∑ i ∈ Finset.range 423, stT277 (i+1)) + stT277 424 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 423
    simpa using h
  have hprev := st277_p423
  have hstep := st277_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p425 : ((11236294255847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT277 (i+1))
      = (∑ i ∈ Finset.range 424, stT277 (i+1)) + stT277 425 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 424
    simpa using h
  have hprev := st277_p424
  have hstep := st277_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p426 : ((5842732479213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT277 (i+1))
      = (∑ i ∈ Finset.range 425, stT277 (i+1)) + stT277 426 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 425
    simpa using h
  have hprev := st277_p425
  have hstep := st277_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p427 : ((11933083311933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT277 (i+1))
      = (∑ i ∈ Finset.range 426, stT277 (i+1)) + stT277 427 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 426
    simpa using h
  have hprev := st277_p426
  have hstep := st277_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p428 : ((11879643002031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT277 (i+1))
      = (∑ i ∈ Finset.range 427, stT277 (i+1)) + stT277 428 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 427
    simpa using h
  have hprev := st277_p427
  have hstep := st277_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p429 : ((5773993191873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT277 (i+1))
      = (∑ i ∈ Finset.range 428, stT277 (i+1)) + stT277 429 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 428
    simpa using h
  have hprev := st277_p428
  have hstep := st277_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p430 : ((11072561817523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT277 (i+1))
      = (∑ i ∈ Finset.range 429, stT277 (i+1)) + stT277 430 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 429
    simpa using h
  have hprev := st277_p429
  have hstep := st277_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p431 : ((10644125575303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT277 (i+1))
      = (∑ i ∈ Finset.range 430, stT277 (i+1)) + stT277 431 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 430
    simpa using h
  have hprev := st277_p430
  have hstep := st277_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p432 : ((2086611312271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT277 (i+1))
      = (∑ i ∈ Finset.range 431, stT277 (i+1)) + stT277 432 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 431
    simpa using h
  have hprev := st277_p431
  have hstep := st277_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p433 : ((5261043146863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT277 (i+1))
      = (∑ i ∈ Finset.range 432, stT277 (i+1)) + stT277 433 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 432
    simpa using h
  have hprev := st277_p432
  have hstep := st277_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p434 : ((5437388177473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT277 (i+1))
      = (∑ i ∈ Finset.range 433, stT277 (i+1)) + stT277 434 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 433
    simpa using h
  have hprev := st277_p433
  have hstep := st277_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p435 : ((454057053821/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT277 (i+1))
      = (∑ i ∈ Finset.range 434, stT277 (i+1)) + stT277 435 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 434
    simpa using h
  have hprev := st277_p434
  have hstep := st277_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p436 : ((11765062545799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT277 (i+1))
      = (∑ i ∈ Finset.range 435, stT277 (i+1)) + stT277 436 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 435
    simpa using h
  have hprev := st277_p435
  have hstep := st277_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p437 : ((2390975380527/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT277 (i+1))
      = (∑ i ∈ Finset.range 436, stT277 (i+1)) + stT277 437 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 436
    simpa using h
  have hprev := st277_p436
  have hstep := st277_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p438 : ((473928343563/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT277 (i+1))
      = (∑ i ∈ Finset.range 437, stT277 (i+1)) + stT277 438 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 437
    simpa using h
  have hprev := st277_p437
  have hstep := st277_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p439 : ((2297497934523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT277 (i+1))
      = (∑ i ∈ Finset.range 438, stT277 (i+1)) + stT277 439 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 438
    simpa using h
  have hprev := st277_p438
  have hstep := st277_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p440 : ((440496191267/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT277 (i+1))
      = (∑ i ∈ Finset.range 439, stT277 (i+1)) + stT277 440 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 439
    simpa using h
  have hprev := st277_p439
  have hstep := st277_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p441 : ((10605192905171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT277 (i+1))
      = (∑ i ∈ Finset.range 440, stT277 (i+1)) + stT277 441 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 440
    simpa using h
  have hprev := st277_p440
  have hstep := st277_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p442 : ((10420674651767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT277 (i+1))
      = (∑ i ∈ Finset.range 441, stT277 (i+1)) + stT277 442 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 441
    simpa using h
  have hprev := st277_p441
  have hstep := st277_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p443 : ((10527885551209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT277 (i+1))
      = (∑ i ∈ Finset.range 442, stT277 (i+1)) + stT277 443 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 442
    simpa using h
  have hprev := st277_p442
  have hstep := st277_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p444 : ((10885104683011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT277 (i+1))
      = (∑ i ∈ Finset.range 443, stT277 (i+1)) + stT277 444 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 443
    simpa using h
  have hprev := st277_p443
  have hstep := st277_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p445 : ((11356970972191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT277 (i+1))
      = (∑ i ∈ Finset.range 444, stT277 (i+1)) + stT277 445 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 444
    simpa using h
  have hprev := st277_p444
  have hstep := st277_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p446 : ((588317876357/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT277 (i+1))
      = (∑ i ∈ Finset.range 445, stT277 (i+1)) + stT277 446 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 445
    simpa using h
  have hprev := st277_p445
  have hstep := st277_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p447 : ((1495117132193/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT277 (i+1))
      = (∑ i ∈ Finset.range 446, stT277 (i+1)) + stT277 447 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 446
    simpa using h
  have hprev := st277_p446
  have hstep := st277_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p448 : ((1483672003707/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT277 (i+1))
      = (∑ i ∈ Finset.range 447, stT277 (i+1)) + stT277 448 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 447
    simpa using h
  have hprev := st277_p447
  have hstep := st277_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p449 : ((2881675262409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT277 (i+1))
      = (∑ i ∈ Finset.range 448, stT277 (i+1)) + stT277 449 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 448
    simpa using h
  have hprev := st277_p448
  have hstep := st277_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p450 : ((11060015285091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT277 (i+1))
      = (∑ i ∈ Finset.range 449, stT277 (i+1)) + stT277 450 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 449
    simpa using h
  have hprev := st277_p449
  have hstep := st277_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p451 : ((10640790924019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT277 (i+1))
      = (∑ i ∈ Finset.range 450, stT277 (i+1)) + stT277 451 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 450
    simpa using h
  have hprev := st277_p450
  have hstep := st277_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p452 : ((1302717093863/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT277 (i+1))
      = (∑ i ∈ Finset.range 451, stT277 (i+1)) + stT277 452 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 451
    simpa using h
  have hprev := st277_p451
  have hstep := st277_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p453 : ((1310198473643/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT277 (i+1))
      = (∑ i ∈ Finset.range 452, stT277 (i+1)) + stT277 453 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 452
    simpa using h
  have hprev := st277_p452
  have hstep := st277_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p454 : ((10797527115607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT277 (i+1))
      = (∑ i ∈ Finset.range 453, stT277 (i+1)) + stT277 454 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 453
    simpa using h
  have hprev := st277_p453
  have hstep := st277_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p455 : ((5627364399161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT277 (i+1))
      = (∑ i ∈ Finset.range 454, stT277 (i+1)) + stT277 455 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 454
    simpa using h
  have hprev := st277_p454
  have hstep := st277_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p456 : ((5844325253491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT277 (i+1))
      = (∑ i ∈ Finset.range 455, stT277 (i+1)) + stT277 456 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 455
    simpa using h
  have hprev := st277_p455
  have hstep := st277_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p457 : ((5972225894981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT277 (i+1))
      = (∑ i ∈ Finset.range 456, stT277 (i+1)) + stT277 457 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 456
    simpa using h
  have hprev := st277_p456
  have hstep := st277_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p458 : ((1491487205859/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT277 (i+1))
      = (∑ i ∈ Finset.range 457, stT277 (i+1)) + stT277 458 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 457
    simpa using h
  have hprev := st277_p457
  have hstep := st277_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p459 : ((5828256662241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT277 (i+1))
      = (∑ i ∈ Finset.range 458, stT277 (i+1)) + stT277 459 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 458
    simpa using h
  have hprev := st277_p458
  have hstep := st277_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p460 : ((5608231871541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT277 (i+1))
      = (∑ i ∈ Finset.range 459, stT277 (i+1)) + stT277 460 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 459
    simpa using h
  have hprev := st277_p459
  have hstep := st277_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p461 : ((538344699969/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT277 (i+1))
      = (∑ i ∈ Finset.range 460, stT277 (i+1)) + stT277 461 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 460
    simpa using h
  have hprev := st277_p460
  have hstep := st277_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p462 : ((10465001073381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT277 (i+1))
      = (∑ i ∈ Finset.range 461, stT277 (i+1)) + stT277 462 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 461
    simpa using h
  have hprev := st277_p461
  have hstep := st277_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p463 : ((10415283652921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT277 (i+1))
      = (∑ i ∈ Finset.range 462, stT277 (i+1)) + stT277 463 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 462
    simpa using h
  have hprev := st277_p462
  have hstep := st277_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p464 : ((10633944857539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT277 (i+1))
      = (∑ i ∈ Finset.range 463, stT277 (i+1)) + stT277 464 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 463
    simpa using h
  have hprev := st277_p463
  have hstep := st277_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p465 : ((11044405853671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT277 (i+1))
      = (∑ i ∈ Finset.range 464, stT277 (i+1)) + stT277 465 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 464
    simpa using h
  have hprev := st277_p464
  have hstep := st277_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p466 : ((1438095976357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT277 (i+1))
      = (∑ i ∈ Finset.range 465, stT277 (i+1)) + stT277 466 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 465
    simpa using h
  have hprev := st277_p465
  have hstep := st277_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p467 : ((1482151518877/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT277 (i+1))
      = (∑ i ∈ Finset.range 466, stT277 (i+1)) + stT277 467 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 466
    simpa using h
  have hprev := st277_p466
  have hstep := st277_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p468 : ((5991003122883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT277 (i+1))
      = (∑ i ∈ Finset.range 467, stT277 (i+1)) + stT277 468 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 467
    simpa using h
  have hprev := st277_p467
  have hstep := st277_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p469 : ((591883796649/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT277 (i+1))
      = (∑ i ∈ Finset.range 468, stT277 (i+1)) + stT277 469 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 468
    simpa using h
  have hprev := st277_p468
  have hstep := st277_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p470 : ((5737049115129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT277 (i+1))
      = (∑ i ∈ Finset.range 469, stT277 (i+1)) + stT277 470 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 469
    simpa using h
  have hprev := st277_p469
  have hstep := st277_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p471 : ((5507284084281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT277 (i+1))
      = (∑ i ∈ Finset.range 470, stT277 (i+1)) + stT277 471 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 470
    simpa using h
  have hprev := st277_p470
  have hstep := st277_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p472 : ((5306782171193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT277 (i+1))
      = (∑ i ∈ Finset.range 471, stT277 (i+1)) + stT277 472 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 471
    simpa using h
  have hprev := st277_p471
  have hstep := st277_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p473 : ((10404771007291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT277 (i+1))
      = (∑ i ∈ Finset.range 472, stT277 (i+1)) + stT277 473 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 472
    simpa using h
  have hprev := st277_p472
  have hstep := st277_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p474 : ((5228435324213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT277 (i+1))
      = (∑ i ∈ Finset.range 473, stT277 (i+1)) + stT277 474 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 473
    simpa using h
  have hprev := st277_p473
  have hstep := st277_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p475 : ((21503113387/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT277 (i+1))
      = (∑ i ∈ Finset.range 474, stT277 (i+1)) + stT277 475 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 474
    simpa using h
  have hprev := st277_p474
  have hstep := st277_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p476 : ((447625743071/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT277 (i+1))
      = (∑ i ∈ Finset.range 475, stT277 (i+1)) + stT277 476 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 475
    simpa using h
  have hprev := st277_p475
  have hstep := st277_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p477 : ((11629298061891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT277 (i+1))
      = (∑ i ∈ Finset.range 476, stT277 (i+1)) + stT277 477 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 476
    simpa using h
  have hprev := st277_p476
  have hstep := st277_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p478 : ((1490497223247/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT277 (i+1))
      = (∑ i ∈ Finset.range 477, stT277 (i+1)) + stT277 478 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 477
    simpa using h
  have hprev := st277_p477
  have hstep := st277_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p479 : ((5989610533671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT277 (i+1))
      = (∑ i ∈ Finset.range 478, stT277 (i+1)) + stT277 479 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 478
    simpa using h
  have hprev := st277_p478
  have hstep := st277_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p480 : ((235560280739/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT277 (i+1))
      = (∑ i ∈ Finset.range 479, stT277 (i+1)) + stT277 480 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 479
    simpa using h
  have hprev := st277_p479
  have hstep := st277_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p481 : ((113864119321/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT277 (i+1))
      = (∑ i ∈ Finset.range 480, stT277 (i+1)) + stT277 481 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 480
    simpa using h
  have hprev := st277_p480
  have hstep := st277_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p482 : ((109312199993/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT277 (i+1))
      = (∑ i ∈ Finset.range 481, stT277 (i+1)) + stT277 482 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 481
    simpa using h
  have hprev := st277_p481
  have hstep := st277_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p483 : ((2639659584497/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT277 (i+1))
      = (∑ i ∈ Finset.range 482, stT277 (i+1)) + stT277 483 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 482
    simpa using h
  have hprev := st277_p482
  have hstep := st277_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p484 : ((5193665657119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT277 (i+1))
      = (∑ i ∈ Finset.range 483, stT277 (i+1)) + stT277 484 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 483
    simpa using h
  have hprev := st277_p483
  have hstep := st277_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p485 : ((5235491732669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT277 (i+1))
      = (∑ i ∈ Finset.range 484, stT277 (i+1)) + stT277 485 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 484
    simpa using h
  have hprev := st277_p484
  have hstep := st277_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p486 : ((431284428127/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT277 (i+1))
      = (∑ i ∈ Finset.range 485, stT277 (i+1)) + stT277 486 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 485
    simpa using h
  have hprev := st277_p485
  have hstep := st277_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p487 : ((2244328257491/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT277 (i+1))
      = (∑ i ∈ Finset.range 486, stT277 (i+1)) + stT277 487 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 486
    simpa using h
  have hprev := st277_p486
  have hstep := st277_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p488 : ((11650932583941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT277 (i+1))
      = (∑ i ∈ Finset.range 487, stT277 (i+1)) + stT277 488 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 487
    simpa using h
  have hprev := st277_p487
  have hstep := st277_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p489 : ((5967821539003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT277 (i+1))
      = (∑ i ∈ Finset.range 488, stT277 (i+1)) + stT277 489 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 488
    simpa using h
  have hprev := st277_p488
  have hstep := st277_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p490 : ((5993775652359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT277 (i+1))
      = (∑ i ∈ Finset.range 489, stT277 (i+1)) + stT277 490 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 489
    simpa using h
  have hprev := st277_p489
  have hstep := st277_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p491 : ((92120456883/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT277 (i+1))
      = (∑ i ∈ Finset.range 490, stT277 (i+1)) + stT277 491 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 490
    simpa using h
  have hprev := st277_p490
  have hstep := st277_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p492 : ((11408867400959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT277 (i+1))
      = (∑ i ∈ Finset.range 491, stT277 (i+1)) + stT277 492 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 491
    simpa using h
  have hprev := st277_p491
  have hstep := st277_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p493 : ((10958471836217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT277 (i+1))
      = (∑ i ∈ Finset.range 492, stT277 (i+1)) + stT277 493 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 492
    simpa using h
  have hprev := st277_p492
  have hstep := st277_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p494 : ((10578706173677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT277 (i+1))
      = (∑ i ∈ Finset.range 493, stT277 (i+1)) + stT277 494 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 493
    simpa using h
  have hprev := st277_p493
  have hstep := st277_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p495 : ((10385375135099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT277 (i+1))
      = (∑ i ∈ Finset.range 494, stT277 (i+1)) + stT277 495 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 494
    simpa using h
  have hprev := st277_p494
  have hstep := st277_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p496 : ((5218316107057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT277 (i+1))
      = (∑ i ∈ Finset.range 495, stT277 (i+1)) + stT277 496 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 495
    simpa using h
  have hprev := st277_p495
  have hstep := st277_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p497 : ((10715989276499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT277 (i+1))
      = (∑ i ∈ Finset.range 496, stT277 (i+1)) + stT277 497 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 496
    simpa using h
  have hprev := st277_p496
  have hstep := st277_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p498 : ((11138175216779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT277 (i+1))
      = (∑ i ∈ Finset.range 497, stT277 (i+1)) + stT277 498 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 497
    simpa using h
  have hprev := st277_p497
  have hstep := st277_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p499 : ((11575602686319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT277 (i+1))
      = (∑ i ∈ Finset.range 498, stT277 (i+1)) + stT277 499 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 498
    simpa using h
  have hprev := st277_p498
  have hstep := st277_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_p500 : ((371784070263/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT277 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT277 (i+1))
      = (∑ i ∈ Finset.range 499, stT277 (i+1)) + stT277 500 := by
    have h := Finset.sum_range_succ (fun i => stT277 (i+1)) 499
    simpa using h
  have hprev := st277_p499
  have hstep := st277_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st277_s500 :
    |Real.sin (((277 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))
      - ((347547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1921377/10000000) (δ := 13969/1000000000) (ψ := -182979/200000) 277 274
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 277`** (evaluated boundary). -/
theorem station_277_sign : hardyG ((((277:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 277 500 (by norm_num) (by norm_num)
    ((-182979/200000 : ℚ) : ℝ)
  have hchain := st277_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT277 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((277 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-182979/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st277_c500
  have hsinb := abs_le.mp st277_s500
  have hbdy_lo : ((-17254801636643/306917000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((277 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-182979/200000 : ℚ) : ℝ))) / 2
          - ((((277:ℕ)):ℝ))
            * Real.sin (((277 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-182979/200000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((277:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((277:ℝ) * Real.log (500:ℝ) - ((-182979/200000 : ℚ) : ℝ))) / 2
        - ((277:ℝ)) * Real.sin ((277:ℝ) * Real.log (500:ℝ) - ((-182979/200000 : ℚ) : ℝ))
        ≥ ((-77165749/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((277:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-77165749/400000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-77165749/400000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-77165749/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((277:ℕ)):ℝ))+1) * (((((277:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((3011042892067/5000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((371784070263/312500000000 : ℚ) : ℝ) + ((-17254801636643/306917000000000 : ℚ) : ℝ)
      - ((3011042892067/5000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-182979/200000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((277:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-182979/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((277:ℕ)):ℝ)))).re
      - Real.sin ((-182979/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((277:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((277:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((277:ℕ)):ℝ))
      = (((((277:ℕ)):ℝ)) * (Real.log ((((277:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((277:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_277
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
  have hθwin : |(((-182979/200000 : ℚ) : ℝ) + ((62:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((277:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((277:ℕ)):ℝ)))
    (φ := ((-182979/200000 : ℚ) : ℝ) + ((62:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-182979/200000 : ℚ) : ℝ) + ((62:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-182979/200000 : ℚ)) : ℝ) - Real.pi) + ((62:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-182979/200000 : ℚ)) : ℝ) - Real.pi) 62).1,
    (cos_sin_shift ((((-182979/200000 : ℚ)) : ℝ) - Real.pi) 62).2]
  exact cos_sin_flip ((-182979/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_277_sign
end AxiomAudit
