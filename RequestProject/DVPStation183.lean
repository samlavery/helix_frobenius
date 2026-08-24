import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 183` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT183 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((183 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))

theorem st183_c1 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((989199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183889/5000000) (δ := 201/1000000000) (ψ := -147111/1000000) 183 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t1 : ((989149/1000000 : ℚ) : ℝ) ≤ stT183 1 := by
  have hc : ((989149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((989149/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((989149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c2 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((59781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3323333/10000000) (δ := 4629/500000000) (ψ := -147111/1000000) 183 20
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t2 : ((845254135979/5000000000000 : ℚ) : ℝ) ≤ stT183 2 := by
  have hc : ((119537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((845254135979/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((119537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c3 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((991403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328057/10000000) (δ := 1159/125000000) (ψ := -147111/1000000) 183 32
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t3 : ((2861789264103/5000000000000 : ℚ) : ℝ) ≤ stT183 3 := by
  have hc : ((991353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2861789264103/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((991353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c4 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-808011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49054/78125) (δ := 9189/1000000000) (ψ := -147111/1000000) 183 40
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t4 : ((-4040305808061/10000000000000 : ℚ) : ℝ) ≤ stT183 4 := by
  have hc : ((-808061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4040305808061/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-808061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c5 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((804803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794317/5000000) (δ := 2291/250000000) (ψ := -147111/1000000) 183 47
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t5 : ((719792811531/2000000000000 : ℚ) : ℝ) ≤ stT183 5 := by
  have hc : ((804753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((719792811531/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((804753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c6 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((254511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 820909/2500000) (δ := 367/40000000) (ψ := -147111/1000000) 183 52
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t6 : ((519416226101/5000000000000 : ℚ) : ℝ) ≤ stT183 6 := by
  have hc : ((254461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519416226101/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((254461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c7 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-316557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -946447/2000000) (δ := 9211/1000000000) (ψ := -147111/1000000) 183 57
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t7 : ((-239332412903/2000000000000 : ℚ) : ℝ) ≤ stT183 7 := by
  have hc : ((-316607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239332412903/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-316607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c8 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-851371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6473473/10000000) (δ := 579/62500000) (ψ := -147111/1000000) 183 61
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t8 : ((-1505113946907/5000000000000 : ℚ) : ℝ) ≤ stT183 8 := by
  have hc : ((-851421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1505113946907/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-851421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c9 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((198671/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7209/250000) (δ := 9161/1000000000) (ψ := -147111/1000000) 183 64
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t9 : ((662203267113/2000000000000 : ℚ) : ℝ) ≤ stT183 9 := by
  have hc : ((198661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((662203267113/2000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((198661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c10 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((427107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1366899/10000000) (δ := 9183/1000000000) (ψ := -147111/1000000) 183 67
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t10 : ((675275792857/2500000000000 : ℚ) : ℝ) ≤ stT183 10 := by
  have hc : ((213541/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((675275792857/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((213541/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c11 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((651657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1076287/5000000) (δ := 1163/125000000) (ψ := -147111/1000000) 183 70
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t11 : ((1964668736591/10000000000000 : ℚ) : ℝ) ≤ stT183 11 := by
  have hc : ((651607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1964668736591/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((651607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c12 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-399277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1247843/2000000) (δ := 4659/500000000) (ψ := -147111/1000000) 183 72
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t12 : ((-18010716361/78125000000 : ℚ) : ℝ) ≤ stT183 12 := by
  have hc : ((-199651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18010716361/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-199651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c13 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-2107/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213257/500000) (δ := 9163/1000000000) (ψ := -147111/1000000) 183 75
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t13 : ((-187069868949/5000000000000 : ℚ) : ℝ) ≤ stT183 13 := by
  have hc : ((-67449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187069868949/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-67449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c14 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((75793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1776657/10000000) (δ := 9349/1000000000) (ψ := -147111/1000000) 183 77
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t14 : ((12659494891/62500000000 : ℚ) : ℝ) ≤ stT183 14 := by
  have hc : ((18947/25000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12659494891/62500000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((18947/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c15 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((795277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1628331/10000000) (δ := 9269/1000000000) (ψ := -147111/1000000) 183 79
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t15 : ((513316642819/2500000000000 : ℚ) : ℝ) ≤ stT183 15 := by
  have hc : ((795227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((513316642819/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((795227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c16 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((162909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1758947/5000000) (δ := 9183/1000000000) (ψ := -147111/1000000) 183 81
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t16 : ((162859/4000000 : ℚ) : ℝ) ≤ stT183 16 := by
  have hc : ((162859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162859/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((162859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c17 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-965779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3599033/5000000) (δ := 9197/1000000000) (ψ := -147111/1000000) 183 83
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t17 : ((-2342480125953/10000000000000 : ℚ) : ℝ) ≤ stT183 17 := by
  have hc : ((-965829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2342480125953/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-965829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c18 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((134917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3243939/10000000) (δ := 1861/200000000) (ψ := -147111/1000000) 183 84
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t18 : ((39742926453/625000000000 : ℚ) : ℝ) ≤ stT183 18 := by
  have hc : ((33723/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39742926453/625000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((33723/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c19 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((1219/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -859061/2500000) (δ := 287/31250000) (ψ := -147111/1000000) 183 86
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t19 : ((44733767343/1000000000000 : ℚ) : ℝ) ≤ stT183 19 := by
  have hc : ((19499/100000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44733767343/1000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((19499/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c20 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-4923/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2161239/5000000) (δ := 4663/500000000) (ψ := -147111/1000000) 183 87
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t20 : ((-44046626481/1250000000000 : ℚ) : ℝ) ≤ stT183 20 := by
  have hc : ((-78793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44046626481/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-78793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c21 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-331579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1192983/2500000) (δ := 467/50000000) (ψ := -147111/1000000) 183 89
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t21 : ((-723673839591/10000000000000 : ℚ) : ℝ) ≤ stT183 21 := by
  have hc : ((-331629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-723673839591/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-331629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c22 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((948857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200751/2500000) (δ := 1851/200000000) (ψ := -147111/1000000) 183 90
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t22 : ((2022863165649/10000000000000 : ℚ) : ℝ) ≤ stT183 22 := by
  have hc : ((948807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2022863165649/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((948807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c23 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-566209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5431739/10000000) (δ := 2337/250000000) (ψ := -147111/1000000) 183 91
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t23 : ((-236146424511/2000000000000 : ℚ) : ℝ) ≤ stT183 23 := by
  have hc : ((-566259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236146424511/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-566259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c24 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-859593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -651317/1000000) (δ := 9169/1000000000) (ψ := -147111/1000000) 183 93
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t24 : ((-877369698303/5000000000000 : ℚ) : ℝ) ≤ stT183 24 := by
  have hc : ((-859643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-877369698303/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-859643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c25 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((9511/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -886267/2500000) (δ := 2319/250000000) (ψ := -147111/1000000) 183 94
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t25 : ((76063/2500000 : ℚ) : ℝ) ≤ stT183 25 := by
  have hc : ((76063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76063/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((76063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c26 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((865913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1309561/10000000) (δ := 2321/250000000) (ψ := -147111/1000000) 183 95
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t26 : ((1698096746943/10000000000000 : ℚ) : ℝ) ≤ stT183 26 := by
  have hc : ((865863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1698096746943/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((865863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c27 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((995057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248663/10000000) (δ := 9291/1000000000) (ψ := -147111/1000000) 183 96
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t27 : ((3829781943/20000000000 : ℚ) : ℝ) ≤ stT183 27 := by
  have hc : ((995007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3829781943/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((995007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c28 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((890857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589461/5000000) (δ := 1841/200000000) (ψ := -147111/1000000) 183 97
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t28 : ((841733333177/5000000000000 : ℚ) : ℝ) ≤ stT183 28 := by
  have hc : ((890807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((841733333177/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((890807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c29 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((204899/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1525229/10000000) (δ := 1861/200000000) (ψ := -147111/1000000) 183 98
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t29 : ((760929201669/5000000000000 : ℚ) : ℝ) ≤ stT183 29 := by
  have hc : ((409773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760929201669/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((409773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c30 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((862361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 663601/5000000) (δ := 291/31250000) (ψ := -147111/1000000) 183 99
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t30 : ((1574356547451/10000000000000 : ℚ) : ℝ) ≤ stT183 30 := by
  have hc : ((862311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1574356547451/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((862311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c31 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((193869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310309/5000000) (δ := 9319/1000000000) (ψ := -147111/1000000) 183 100
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t31 : ((348181038527/2000000000000 : ℚ) : ℝ) ≤ stT183 31 := by
  have hc : ((193859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348181038527/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((193859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c32 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((974811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112463/2000000) (δ := 9327/1000000000) (ψ := -147111/1000000) 183 101
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t32 : ((861574676963/5000000000000 : ℚ) : ℝ) ≤ stT183 32 := by
  have hc : ((974761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((861574676963/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((974761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c33 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((639531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137017/625000) (δ := 9269/1000000000) (ψ := -147111/1000000) 183 102
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t33 : ((139149147157/1250000000000 : ℚ) : ℝ) ≤ stT183 33 := by
  have hc : ((639481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139149147157/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((639481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c34 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-15733/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4242487/10000000) (δ := 9341/1000000000) (ψ := -147111/1000000) 183 103
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t34 : ((-53985186801/2500000000000 : ℚ) : ℝ) ≤ stT183 34 := by
  have hc : ((-62957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53985186801/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-62957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c35 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-893317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6688669/10000000) (δ := 2337/250000000) (ψ := -147111/1000000) 183 104
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t35 : ((-1510066280403/10000000000000 : ℚ) : ℝ) ≤ stT183 35 := by
  have hc : ((-893367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1510066280403/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-893367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c36 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-24653/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6199517/10000000) (δ := 1851/200000000) (ψ := -147111/1000000) 183 104
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t36 : ((-657455131491/5000000000000 : ℚ) : ℝ) ≤ stT183 36 := by
  have hc : ((-394473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657455131491/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-394473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c37 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((176211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756649/2500000) (δ := 2337/250000000) (ψ := -147111/1000000) 183 105
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t37 : ((144823922977/2500000000000 : ℚ) : ℝ) ≤ stT183 37 := by
  have hc : ((88093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144823922977/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((88093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c38 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((490787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96133/2000000) (δ := 9263/1000000000) (ψ := -147111/1000000) 183 106
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t38 : ((199030246767/1250000000000 : ℚ) : ℝ) ≤ stT183 38 := by
  have hc : ((245381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199030246767/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((245381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c39 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-37641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4304837/10000000) (δ := 927/100000000) (ψ := -147111/1000000) 183 107
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t39 : ((-60293871787/2500000000000 : ℚ) : ℝ) ≤ stT183 39 := by
  have hc : ((-75307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60293871787/2500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-75307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c40 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-486791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 909757/1250000) (δ := 9233/1000000000) (ψ := -147111/1000000) 183 107
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t40 : ((-24053867607/156250000000 : ℚ) : ℝ) ≤ stT183 40 := by
  have hc : ((-15213/15625 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24053867607/156250000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-15213/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c41 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((205711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2866957/10000000) (δ := 4663/500000000) (ψ := -147111/1000000) 183 108
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t41 : ((160613718291/2500000000000 : ℚ) : ℝ) ≤ stT183 41 := by
  have hc : ((102843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160613718291/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((102843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c42 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((186869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -908177/5000000) (δ := 9219/1000000000) (ψ := -147111/1000000) 183 109
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t42 : ((576651491529/5000000000000 : ℚ) : ℝ) ≤ stT183 42 := by
  have hc : ((373713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((576651491529/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((373713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c43 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-113203/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6759113/10000000) (δ := 9291/1000000000) (ψ := -147111/1000000) 183 110
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t43 : ((-345285042641/2500000000000 : ℚ) : ℝ) ≤ stT183 43 := by
  have hc : ((-452837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345285042641/2500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-452837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c44 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((4207/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3758583/10000000) (δ := 9191/1000000000) (ψ := -147111/1000000) 183 110
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t44 : ((12675153959/1250000000000 : ℚ) : ℝ) ≤ stT183 44 := by
  have hc : ((33631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12675153959/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((33631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c45 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((785539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834037/5000000) (δ := 4649/500000000) (ψ := -147111/1000000) 183 111
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t45 : ((1170937092679/10000000000000 : ℚ) : ℝ) ≤ stT183 45 := by
  have hc : ((785489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1170937092679/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((785489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c46 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-488667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7320691/10000000) (δ := 9197/1000000000) (ψ := -147111/1000000) 183 112
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t46 : ((-9006715733/62500000000 : ℚ) : ℝ) ≤ stT183 46 := by
  have hc : ((-122173/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9006715733/62500000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-122173/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c47 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((534081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2518441/10000000) (δ := 9297/1000000000) (ψ := -147111/1000000) 183 112
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t47 : ((778963784119/10000000000000 : ℚ) : ℝ) ≤ stT183 47 := by
  have hc : ((534031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((778963784119/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((534031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c48 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((147223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3557591/10000000) (δ := 9313/1000000000) (ψ := -147111/1000000) 183 113
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t48 : ((1699406631/80000000000 : ℚ) : ℝ) ≤ stT183 48 := by
  have hc : ((147173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1699406631/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((147173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c49 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-70291/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5875693/10000000) (δ := 9313/1000000000) (ψ := -147111/1000000) 183 113
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t49 : ((-3138215541/31250000000 : ℚ) : ℝ) ≤ stT183 49 := by
  have hc : ((-8787/12500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3138215541/31250000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-8787/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c50 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((972329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58949/1000000) (δ := 9283/1000000000) (ψ := -147111/1000000) 183 114
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t50 : ((1375009601427/10000000000000 : ℚ) : ℝ) ≤ stT183 50 := by
  have hc : ((972279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1375009601427/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((972279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c51 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-38791/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7237763/10000000) (δ := 9327/1000000000) (ψ := -147111/1000000) 183 115
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t51 : ((-54321100833/400000000000 : ℚ) : ℝ) ≤ stT183 51 := by
  have hc : ((-38793/40000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54321100833/400000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-38793/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c52 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((98871/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1646017/10000000) (δ := 2319/250000000) (ψ := -147111/1000000) 183 115
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t52 : ((2193611073/20000000000 : ℚ) : ℝ) ≤ stT183 52 := by
  have hc : ((395459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2193611073/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((395459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c53 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-538083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2673697/5000000) (δ := 4667/500000000) (ψ := -147111/1000000) 183 116
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t53 : ((-369591358799/5000000000000 : ℚ) : ℝ) ≤ stT183 53 := by
  have hc : ((-538133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369591358799/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-538133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c54 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((28509/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3204241/10000000) (δ := 9269/1000000000) (ψ := -147111/1000000) 183 116
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t54 : ((4848626601/125000000000 : ℚ) : ℝ) ≤ stT183 54 := by
  have hc : ((3563/12500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4848626601/125000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((3563/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c55 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-72743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4109009/10000000) (δ := 9261/1000000000) (ψ := -147111/1000000) 183 117
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t55 : ((-245385203/25000000000 : ℚ) : ℝ) ≤ stT183 55 := by
  have hc : ((-72793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245385203/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-72793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c56 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-8289/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 826891/2000000) (δ := 9161/1000000000) (ψ := -147111/1000000) 183 117
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t56 : ((-5541665129/500000000000 : ℚ) : ℝ) ≤ stT183 56 := by
  have hc : ((-4147/50000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5541665129/500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-4147/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c57 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((179443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3475941/10000000) (δ := 9249/1000000000) (ψ := -147111/1000000) 183 118
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t57 : ((59402942269/2500000000000 : ℚ) : ℝ) ≤ stT183 57 := by
  have hc : ((179393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59402942269/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((179393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c58 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-219719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4480807/10000000) (δ := 4627/500000000) (ψ := -147111/1000000) 183 118
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t58 : ((-57714196397/2000000000000 : ℚ) : ℝ) ≤ stT183 58 := by
  have hc : ((-219769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57714196397/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-219769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c59 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((51677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -851617/2500000) (δ := 2289/250000000) (ψ := -147111/1000000) 183 119
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t59 : ((134522888481/5000000000000 : ℚ) : ℝ) ≤ stT183 59 := by
  have hc : ((103329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134522888481/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((103329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c60 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-35459/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214139/500000) (δ := 9247/1000000000) (ψ := -147111/1000000) 183 119
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t60 : ((-18317411657/1000000000000 : ℚ) : ℝ) ≤ stT183 60 := by
  have hc : ((-70943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18317411657/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-70943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c61 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((12791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -965757/2500000) (δ := 9263/1000000000) (ψ := -147111/1000000) 183 120
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t61 : ((510786809/156250000000 : ℚ) : ℝ) ≤ stT183 61 := by
  have hc : ((6383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((510786809/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((6383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c62 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((34969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71523/200000) (δ := 467/50000000) (ψ := -147111/1000000) 183 120
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t62 : ((88789579913/5000000000000 : ℚ) : ℝ) ≤ stT183 62 := by
  have hc : ((69913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88789579913/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((69913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c63 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-346517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -481163/1000000) (δ := 9233/1000000000) (ψ := -147111/1000000) 183 121
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t63 : ((-218316762547/5000000000000 : ℚ) : ℝ) ≤ stT183 63 := by
  have hc : ((-346567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218316762547/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-346567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c64 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((575741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2393217/10000000) (δ := 9333/1000000000) (ψ := -147111/1000000) 183 121
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t64 : ((575691/8000000 : ℚ) : ℝ) ≤ stT183 64 := by
  have hc : ((575691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((575691/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((575691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c65 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-794287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3110787/5000000) (δ := 9277/1000000000) (ψ := -147111/1000000) 183 122
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t65 : ((-246313577319/2500000000000 : ℚ) : ℝ) ≤ stT183 65 := by
  have hc : ((-794337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246313577319/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-794337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c66 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((763/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 763307/10000000) (δ := 9177/1000000000) (ψ := -147111/1000000) 183 122
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t66 : ((5869613409/50000000000 : ℚ) : ℝ) ≤ stT183 66 := by
  have hc : ((9537/10000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5869613409/50000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((9537/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c67 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-498223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3821573/5000000) (δ := 4613/500000000) (ψ := -147111/1000000) 183 122
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t67 : ((-15217677259/125000000000 : ℚ) : ℝ) ≤ stT183 67 := by
  have hc : ((-62281/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15217677259/125000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-62281/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c68 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((870409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1286909/10000000) (δ := 4609/500000000) (ψ := -147111/1000000) 183 123
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t68 : ((527732605701/5000000000000 : ℚ) : ℝ) ≤ stT183 68 := by
  have hc : ((870359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527732605701/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((870359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c69 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-11061/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2696021/5000000) (δ := 4609/500000000) (ψ := -147111/1000000) 183 123
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t69 : ((-6658544129/100000000000 : ℚ) : ℝ) ≤ stT183 69 := by
  have hc : ((-5531/10000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6658544129/100000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-5531/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c70 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((38741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3733091/10000000) (δ := 9211/1000000000) (ψ := -147111/1000000) 183 124
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t70 : ((2892152953/312500000000 : ℚ) : ℝ) ≤ stT183 70 := by
  have hc : ((9679/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2892152953/312500000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((9679/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c71 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((225663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689091/2500000) (δ := 2323/250000000) (ψ := -147111/1000000) 183 124
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t71 : ((133891445639/2500000000000 : ℚ) : ℝ) ≤ stT183 71 := by
  have hc : ((112819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133891445639/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((112819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c72 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-433799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6552867/10000000) (δ := 9299/1000000000) (ψ := -147111/1000000) 183 125
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t72 : ((-998567949/9765625000 : ℚ) : ℝ) ≤ stT183 72 := by
  have hc : ((-13557/15625 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-998567949/9765625000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-13557/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c73 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((497651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242433/10000000) (δ := 1163/125000000) (ψ := -147111/1000000) 183 125
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t73 : ((291213472143/2500000000000 : ℚ) : ℝ) ≤ stT183 73 := by
  have hc : ((248813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291213472143/2500000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((248813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c74 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-366273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5982129/10000000) (δ := 1163/125000000) (ψ := -147111/1000000) 183 125
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t74 : ((-212906500073/2500000000000 : ℚ) : ℝ) ≤ stT183 74 := by
  have hc : ((-183149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212906500073/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-183149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c75 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((136463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1792383/5000000) (δ := 9297/1000000000) (ψ := -147111/1000000) 183 126
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t75 : ((1575160911/100000000000 : ℚ) : ℝ) ≤ stT183 75 := by
  have hc : ((136413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1575160911/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((136413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c76 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((548719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2474913/10000000) (δ := 9297/1000000000) (ψ := -147111/1000000) 183 126
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t76 : ((314683069591/5000000000000 : ℚ) : ℝ) ≤ stT183 76 := by
  have hc : ((548669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((314683069591/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((548669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c77 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-971203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1813141/2500000) (δ := 9213/1000000000) (ψ := -147111/1000000) 183 127
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t77 : ((-553422873159/5000000000000 : ℚ) : ℝ) ≤ stT183 77 := by
  have hc : ((-971253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553422873159/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-971253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c78 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((857861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1349259/10000000) (δ := 929/100000000) (ψ := -147111/1000000) 183 127
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t78 : ((971279665647/10000000000000 : ℚ) : ℝ) ≤ stT183 78 := by
  have hc : ((857811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((971279665647/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((857811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c79 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-218949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2239417/5000000) (δ := 9213/1000000000) (ψ := -147111/1000000) 183 127
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t79 : ((-7699785841/312500000000 : ℚ) : ℝ) ≤ stT183 79 := by
  have hc : ((-218999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7699785841/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-218999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c80 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-72521/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -684291/1250000) (δ := 233/25000000) (ψ := -147111/1000000) 183 128
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t80 : ((-162175862853/2500000000000 : ℚ) : ℝ) ≤ stT183 80 := by
  have hc : ((-290109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162175862853/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-290109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c81 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((996509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41793/2000000) (δ := 9283/1000000000) (ψ := -147111/1000000) 183 128
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t81 : ((1107176555949/10000000000000 : ℚ) : ℝ) ≤ stT183 81 := by
  have hc : ((996459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1107176555949/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((996459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c82 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-687629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 727817/1250000) (δ := 9183/1000000000) (ψ := -147111/1000000) 183 128
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t82 : ((-189853730641/2500000000000 : ℚ) : ℝ) ≤ stT183 82 := by
  have hc : ((-687679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189853730641/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-687679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c83 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-164409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4339887/10000000) (δ := 371/40000000) (ψ := -147111/1000000) 183 129
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t83 : ((-180517270137/10000000000000 : ℚ) : ℝ) ≤ stT183 83 := by
  have hc : ((-164459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180517270137/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-164459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c84 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((448981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 569601/5000000) (δ := 2291/125000000) (ψ := -147111/1000000) 183 129
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t84 : ((122462738271/1250000000000 : ℚ) : ℝ) ≤ stT183 84 := by
  have hc : ((112239/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122462738271/1250000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((112239/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c85 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-216929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6553463/10000000) (δ := 2307/250000000) (ψ := -147111/1000000) 183 129
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t85 : ((-470612497599/5000000000000 : ℚ) : ℝ) ≤ stT183 85 := by
  have hc : ((-433883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470612497599/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-433883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c86 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((771/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190179/500000) (δ := 1867/200000000) (ψ := -147111/1000000) 183 130
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t86 : ((26577525569/5000000000000 : ℚ) : ℝ) ≤ stT183 86 := by
  have hc : ((24647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26577525569/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((24647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c87 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((82859/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1485531/10000000) (δ := 2317/250000000) (ψ := -147111/1000000) 183 130
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t87 : ((2775898989/31250000000 : ℚ) : ℝ) ≤ stT183 87 := by
  have hc : ((41427/50000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2775898989/31250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((41427/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c88 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-897853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3357081/5000000) (δ := 1867/200000000) (ψ := -147111/1000000) 183 130
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t88 : ((-239292047403/2500000000000 : ℚ) : ℝ) ≤ stT183 88 := by
  have hc : ((-897903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239292047403/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-897903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c89 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((41073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95607/250000) (δ := 4671/500000000) (ψ := -147111/1000000) 183 131
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t89 : ((43484256931/10000000000000 : ℚ) : ℝ) ≤ stT183 89 := by
  have hc : ((41023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43484256931/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((41023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c90 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((217573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80469/625000) (δ := 9261/1000000000) (ψ := -147111/1000000) 183 131
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t90 : ((114664391283/1250000000000 : ℚ) : ℝ) ≤ stT183 90 := by
  have hc : ((435121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114664391283/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((435121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c91 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-205701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6342811/10000000) (δ := 9221/500000000) (ψ := -147111/1000000) 183 131
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t91 : ((-86258550539/1000000000000 : ℚ) : ℝ) ≤ stT183 91 := by
  have hc : ((-411427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86258550539/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-411427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c92 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-174353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -545639/1250000) (δ := 9249/1000000000) (ψ := -147111/1000000) 183 132
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t92 : ((-181827858919/10000000000000 : ℚ) : ℝ) ≤ stT183 92 := by
  have hc : ((-174403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181827858919/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-174403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c93 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((121641/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4647/80000) (δ := 9349/1000000000) (ψ := -147111/1000000) 183 132
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t93 : ((504517102589/5000000000000 : ℚ) : ℝ) ≤ stT183 93 := by
  have hc : ((486539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((504517102589/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((486539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c94 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-580053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2736987/5000000) (δ := 4627/500000000) (ψ := -147111/1000000) 183 132
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t94 : ((-299165498233/5000000000000 : ℚ) : ℝ) ≤ stT183 94 := by
  have hc : ((-580103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299165498233/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-580103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c95 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-276631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2696339/5000000) (δ := 1157/125000000) (ψ := -147111/1000000) 183 133
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t95 : ((-17740202889/312500000000 : ℚ) : ℝ) ≤ stT183 95 := by
  have hc : ((-17291/31250 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17740202889/312500000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-17291/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c96 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((485571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602059/10000000) (δ := 9347/1000000000) (ψ := -147111/1000000) 183 133
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t96 : ((12388948963/125000000000 : ℚ) : ℝ) ≤ stT183 96 := by
  have hc : ((242773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12388948963/125000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((242773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c97 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-84671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2069461/5000000) (δ := 9347/1000000000) (ψ := -147111/1000000) 183 133
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t97 : ((-86021213187/10000000000000 : ℚ) : ℝ) ≤ stT183 97 := by
  have hc : ((-84721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86021213187/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-84721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c98 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-11557/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1719173/2500000) (δ := 2291/250000000) (ψ := -147111/1000000) 183 134
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t98 : ((-93399756533/1000000000000 : ℚ) : ℝ) ≤ stT183 98 := by
  have hc : ((-92461/100000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93399756533/1000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-92461/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c99 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((627243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2231969/10000000) (δ := 2291/250000000) (ψ := -147111/1000000) 183 134
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t99 : ((630352171141/10000000000000 : ℚ) : ℝ) ≤ stT183 99 := by
  have hc : ((627193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630352171141/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((627193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c100 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((292297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2366043/10000000) (δ := 9239/1000000000) (ψ := -147111/1000000) 183 134
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t100 : ((18266981733/312500000000 : ℚ) : ℝ) ≤ stT183 100 := by
  have hc : ((18267/31250 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18266981733/312500000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((18267/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c101 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-930781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6918351/10000000) (δ := 9239/1000000000) (ψ := -147111/1000000) 183 134
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t101 : ((-463106108289/5000000000000 : ℚ) : ℝ) ≤ stT183 101 := by
  have hc : ((-930831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463106108289/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-930831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c102 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-177/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -856437/2000000) (δ := 577/62500000) (ψ := -147111/1000000) 183 135
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t102 : ((-701272321/50000000000 : ℚ) : ℝ) ≤ stT183 102 := by
  have hc : ((-2833/20000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-701272321/50000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-2833/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c103 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((498687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181231/10000000) (δ := 9171/1000000000) (ψ := -147111/1000000) 183 135
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t103 : ((245673064899/2500000000000 : ℚ) : ℝ) ≤ stT183 103 := by
  have hc : ((249331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245673064899/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((249331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c104 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-266561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92031/200000) (δ := 577/62500000) (ψ := -147111/1000000) 183 135
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t104 : ((-261433680991/10000000000000 : ℚ) : ℝ) ≤ stT183 104 := by
  have hc : ((-266611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261433680991/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-266611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c105 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-45017/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6728367/10000000) (δ := 369/40000000) (ψ := -147111/1000000) 183 136
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t105 : ((-87869150139/1000000000000 : ℚ) : ℝ) ≤ stT183 105 := by
  have hc : ((-90039/100000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87869150139/1000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-90039/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c106 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((72023/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1195931/5000000) (δ := 373/40000000) (ψ := -147111/1000000) 183 136
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t106 : ((55959031219/1000000000000 : ℚ) : ℝ) ≤ stT183 106 := by
  have hc : ((288067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55959031219/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((288067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c107 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((723741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 475993/2500000) (δ := 4589/500000000) (ψ := -147111/1000000) 183 136
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t107 : ((43726133911/625000000000 : ℚ) : ℝ) ≤ stT183 107 := by
  have hc : ((723691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43726133911/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((723691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c108 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-779039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 307991/500000) (δ := 4589/500000000) (ψ := -147111/1000000) 183 136
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t108 : ((-749679169339/10000000000000 : ℚ) : ℝ) ≤ stT183 108 := by
  have hc : ((-779089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-749679169339/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-779089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c109 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-53273/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5331549/10000000) (δ := 4609/500000000) (ψ := -147111/1000000) 183 137
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t109 : ((-25515553453/500000000000 : ℚ) : ℝ) ≤ stT183 109 := by
  have hc : ((-26639/50000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25515553453/500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-26639/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c110 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((895443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115343/1000000) (δ := 1837/200000000) (ψ := -147111/1000000) 183 137
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t110 : ((426861600283/5000000000000 : ℚ) : ℝ) ≤ stT183 110 := by
  have hc : ((895393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426861600283/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((895393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c111 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((367237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2986899/10000000) (δ := 4609/500000000) (ψ := -147111/1000000) 183 137
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t111 : ((348518111359/10000000000000 : ℚ) : ℝ) ≤ stT183 111 := by
  have hc : ((367187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348518111359/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((367187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c112 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-953673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3545017/5000000) (δ := 1857/200000000) (ψ := -147111/1000000) 183 137
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t112 : ((-56324019211/625000000000 : ℚ) : ℝ) ≤ stT183 112 := by
  have hc : ((-953723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56324019211/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-953723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c113 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-123551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1137803/2500000) (δ := 1149/125000000) (ψ := -147111/1000000) 183 138
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t113 : ((-14531317287/625000000000 : ℚ) : ℝ) ≤ stT183 113 := by
  have hc : ((-15447/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14531317287/625000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-15447/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c114 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((61151/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -520363/10000000) (δ := 9311/1000000000) (ψ := -147111/1000000) 183 138
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t114 : ((91632292011/1000000000000 : ℚ) : ℝ) ≤ stT183 114 := by
  have hc : ((489183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91632292011/1000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((489183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c115 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((179693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 695061/2000000) (δ := 9211/1000000000) (ψ := -147111/1000000) 183 138
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t115 : ((20939727009/1250000000000 : ℚ) : ℝ) ≤ stT183 115 := by
  have hc : ((179643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20939727009/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((179643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c116 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-493039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371817/500000) (δ := 9211/1000000000) (ψ := -147111/1000000) 183 138
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t116 : ((-57224822941/625000000000 : ℚ) : ℝ) ≤ stT183 116 := by
  have hc : ((-61633/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57224822941/625000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-61633/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c117 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-83121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -868907/2000000) (δ := 1163/125000000) (ψ := -147111/1000000) 183 139
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t117 : ((-38434280073/2500000000000 : ℚ) : ℝ) ≤ stT183 117 := by
  have hc : ((-41573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38434280073/2500000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-41573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c118 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((49189/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -450889/10000000) (δ := 9299/1000000000) (ψ := -147111/1000000) 183 139
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t118 : ((45279813051/500000000000 : ℚ) : ℝ) ≤ stT183 118 := by
  have hc : ((98373/100000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45279813051/500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((98373/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c119 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((10269/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1704931/5000000) (δ := 9299/1000000000) (ψ := -147111/1000000) 183 139
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t119 : ((9411280017/500000000000 : ℚ) : ℝ) ≤ stT183 119 := by
  have hc : ((20533/100000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9411280017/500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((20533/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c120 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-484917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7238359/10000000) (δ := 9199/1000000000) (ψ := -147111/1000000) 183 139
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t120 : ((-221344744241/2500000000000 : ℚ) : ℝ) ≤ stT183 120 := by
  have hc : ((-242471/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221344744241/2500000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-242471/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c121 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-146979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4672903/10000000) (δ := 9307/1000000000) (ψ := -147111/1000000) 183 140
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t121 : ((-33410003341/1250000000000 : ℚ) : ℝ) ≤ stT183 121 := by
  have hc : ((-36751/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33410003341/1250000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-36751/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c122 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((934843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18149/200000) (δ := 581/62500000) (ψ := -147111/1000000) 183 140
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t122 : ((846321386101/10000000000000 : ℚ) : ℝ) ≤ stT183 122 := by
  have hc : ((934793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((846321386101/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((934793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c123 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((212921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141363/500000) (δ := 2299/250000000) (ψ := -147111/1000000) 183 140
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t123 : ((5998803857/156250000000 : ℚ) : ℝ) ≤ stT183 123 := by
  have hc : ((6653/15625 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5998803857/156250000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((6653/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c124 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-431681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6531729/10000000) (δ := 2299/250000000) (ψ := -147111/1000000) 183 140
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t124 : ((-193841822031/2500000000000 : ℚ) : ℝ) ≤ stT183 124 := by
  have hc : ((-215853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193841822031/2500000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-215853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c125 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-588987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5501503/10000000) (δ := 9289/1000000000) (ψ := -147111/1000000) 183 141
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t125 : ((-131712796459/2500000000000 : ℚ) : ℝ) ≤ stT183 125 := by
  have hc : ((-589037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131712796459/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-589037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c126 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((368417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1856051/10000000) (δ := 4607/500000000) (ψ := -147111/1000000) 183 141
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t126 : ((4102367263/62500000000 : ℚ) : ℝ) ≤ stT183 126 := by
  have hc : ((46049/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4102367263/62500000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((46049/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c127 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((762121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 440133/2500000) (δ := 9189/1000000000) (ψ := -147111/1000000) 183 141
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t127 : ((169057068569/2500000000000 : ℚ) : ℝ) ≤ stT183 127 := by
  have hc : ((762071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169057068569/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((762071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c128 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-134639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1337199/2500000) (δ := 9189/1000000000) (ψ := -147111/1000000) 183 141
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t128 : ((-59508153213/1250000000000 : ℚ) : ℝ) ≤ stT183 128 := by
  have hc : ((-269303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59508153213/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-269303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c129 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-228061/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6798811/10000000) (δ := 4641/500000000) (ψ := -147111/1000000) 183 142
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t129 : ((-401615082297/5000000000000 : ℚ) : ℝ) ≤ stT183 129 := by
  have hc : ((-456147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-401615082297/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-456147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c130 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((16333/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -816499/2500000) (δ := 4641/500000000) (ψ := -147111/1000000) 183 142
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t130 : ((57288990031/2500000000000 : ℚ) : ℝ) ≤ stT183 130 := by
  have hc : ((130639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57288990031/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((130639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c131 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((248851/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239781/10000000) (δ := 4591/500000000) (ψ := -147111/1000000) 183 142
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t131 : ((54352798201/625000000000 : ℚ) : ℝ) ≤ stT183 131 := by
  have hc : ((497677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54352798201/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((497677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c132 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((41573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1859443/5000000) (δ := 9321/1000000000) (ψ := -147111/1000000) 183 142
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t132 : ((2260180039/312500000000 : ℚ) : ℝ) ≤ stT183 132 := by
  have hc : ((10387/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2260180039/312500000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((10387/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c133 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-962993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 717173/1000000) (δ := 9321/1000000000) (ψ := -147111/1000000) 183 142
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t133 : ((-83506421573/1000000000000 : ℚ) : ℝ) ≤ stT183 133 := by
  have hc : ((-963043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83506421573/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-963043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c134 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-455477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5109261/10000000) (δ := 4607/250000000) (ψ := -147111/1000000) 183 143
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t134 : ((-393515653963/10000000000000 : ℚ) : ℝ) ≤ stT183 134 := by
  have hc : ((-455527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393515653963/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-455527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c135 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((387807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426943/2500000) (δ := 371/40000000) (ψ := -147111/1000000) 183 143
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t135 : ((83437307921/1250000000000 : ℚ) : ℝ) ≤ stT183 135 := by
  have hc : ((193891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83437307921/1250000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((193891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c136 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((785403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104289/625000) (δ := 367/40000000) (ψ := -147111/1000000) 183 143
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t136 : ((168358478669/2500000000000 : ℚ) : ℝ) ≤ stT183 136 := by
  have hc : ((785353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168358478669/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((785353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c137 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-211761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1004063/2000000) (δ := 2307/250000000) (ψ := -147111/1000000) 183 143
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t137 : ((-45235265847/1250000000000 : ℚ) : ℝ) ≤ stT183 137 := by
  have hc : ((-105893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45235265847/1250000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-105893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c138 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-245143/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1840097/2500000) (δ := 1847/200000000) (ψ := -147111/1000000) 183 144
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t138 : ((-417380670927/5000000000000 : ℚ) : ℝ) ≤ stT183 138 := by
  have hc : ((-490311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-417380670927/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-490311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c139 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-52021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4057101/10000000) (δ := 573/62500000) (ψ := -147111/1000000) 183 144
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t139 : ((-44166049419/10000000000000 : ℚ) : ℝ) ≤ stT183 139 := by
  have hc : ((-52071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44166049419/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-52071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c140 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((952027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97189/1250000) (δ := 1847/200000000) (ψ := -147111/1000000) 183 144
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t140 : ((402283584729/5000000000000 : ℚ) : ℝ) ≤ stT183 140 := by
  have hc : ((951977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402283584729/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((951977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c141 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((547453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239349/5000000) (δ := 2317/250000000) (ψ := -147111/1000000) 183 144
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t141 : ((460995983853/10000000000000 : ℚ) : ℝ) ≤ stT183 141 := by
  have hc : ((547403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((460995983853/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((547403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c142 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-654847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2855971/5000000) (δ := 2317/250000000) (ψ := -147111/1000000) 183 144
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t142 : ((-274788887127/5000000000000 : ℚ) : ℝ) ≤ stT183 142 := by
  have hc : ((-654897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274788887127/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-654897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c143 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-227511/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6785469/10000000) (δ := 229/25000000) (ψ := -147111/1000000) 183 145
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t143 : ((-380529868421/5000000000000 : ℚ) : ℝ) ≤ stT183 143 := by
  have hc : ((-455047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-380529868421/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-455047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c144 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((131481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1798667/5000000) (δ := 9343/1000000000) (ψ := -147111/1000000) 183 145
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t144 : ((109525789523/10000000000000 : ℚ) : ℝ) ≤ stT183 144 := by
  have hc : ((131431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109525789523/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((131431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c145 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((492581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215603/5000000) (δ := 463/50000000) (ψ := -147111/1000000) 183 145
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t145 : ((51130637553/625000000000 : ℚ) : ℝ) ≤ stT183 145 := by
  have hc : ((123139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51130637553/625000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((123139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c146 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((116671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1356573/5000000) (δ := 229/25000000) (ψ := -147111/1000000) 183 145
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t146 : ((38618863157/1000000000000 : ℚ) : ℝ) ≤ stT183 146 := by
  have hc : ((233317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38618863157/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((233317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c147 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-86441/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1167199/2000000) (δ := 463/50000000) (ψ := -147111/1000000) 183 145
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t147 : ((-285202271943/5000000000000 : ℚ) : ℝ) ≤ stT183 147 := by
  have hc : ((-345789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285202271943/5000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-345789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c148 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-181501/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1354051/2000000) (δ := 37/4000000) (ψ := -147111/1000000) 183 146
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t148 : ((-29840226889/400000000000 : ℚ) : ℝ) ≤ stT183 148 := by
  have hc : ((-181511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29840226889/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-181511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c149 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((23723/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922351/2500000) (δ := 187/20000000) (ψ := -147111/1000000) 183 146
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t149 : ((38848753251/5000000000000 : ℚ) : ℝ) ≤ stT183 149 := by
  have hc : ((47421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38848753251/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((47421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c150 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((242123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -629233/10000000) (δ := 9253/1000000000) (ψ := -147111/1000000) 183 146
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t150 : ((24710281851/312500000000 : ℚ) : ℝ) ≤ stT183 150 := by
  have hc : ((484221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24710281851/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((484221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c151 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((285009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150667/625000) (δ := 37/4000000) (ψ := -147111/1000000) 183 146
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t151 : ((7247392481/156250000000 : ℚ) : ℝ) ≤ stT183 151 := by
  have hc : ((35623/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7247392481/156250000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((35623/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c152 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-282899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1357623/2500000) (δ := 9153/1000000000) (ψ := -147111/1000000) 183 146
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t152 : ((-14342619987/312500000000 : ℚ) : ℝ) ≤ stT183 152 := by
  have hc : ((-70731/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14342619987/312500000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-70731/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c153 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-121691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7277461/10000000) (δ := 4623/500000000) (ψ := -147111/1000000) 183 147
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t153 : ((-393546027417/5000000000000 : ℚ) : ℝ) ≤ stT183 153 := by
  have hc : ((-486789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393546027417/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-486789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c154 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-73729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2148493/5000000) (δ := 4673/500000000) (ψ := -147111/1000000) 183 147
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t154 : ((-29716334771/2500000000000 : ℚ) : ℝ) ≤ stT183 154 := by
  have hc : ((-36877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29716334771/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-36877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c155 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((215153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1335817/10000000) (δ := 4623/500000000) (ψ := -147111/1000000) 183 147
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t155 : ((345609874539/5000000000000 : ℚ) : ℝ) ≤ stT183 155 := by
  have hc : ((430281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345609874539/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((430281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c156 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((800583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20079/125000) (δ := 9157/1000000000) (ψ := -147111/1000000) 183 147
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t156 : ((1001466783/15625000000 : ℚ) : ℝ) ≤ stT183 156 := by
  have hc : ((800533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1001466783/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((800533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c157 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-238737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4529653/10000000) (δ := 4673/500000000) (ψ := -147111/1000000) 183 147
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t157 : ((-190572800469/10000000000000 : ℚ) : ℝ) ≤ stT183 157 := by
  have hc : ((-238787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190572800469/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-238787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c158 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-19719/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1858603/2500000) (δ := 4673/500000000) (ψ := -147111/1000000) 183 147
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t158 : ((-196105047/2500000000 : ℚ) : ℝ) ≤ stT183 158 := by
  have hc : ((-493/500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196105047/2500000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-493/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c159 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-551399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1346773/2500000) (δ := 9239/1000000000) (ψ := -147111/1000000) 183 148
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t159 : ((-109331933087/2500000000000 : ℚ) : ℝ) ≤ stT183 159 := by
  have hc : ((-551449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109331933087/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-551449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c160 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((66747/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -403/1600) (δ := 9239/1000000000) (ψ := -147111/1000000) 183 148
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t160 : ((211052671947/5000000000000 : ℚ) : ℝ) ≤ stT183 160 := by
  have hc : ((266963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211052671947/5000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((266963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c161 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((991211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41463/1250000) (δ := 2291/250000000) (ψ := -147111/1000000) 183 148
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t161 : ((78114389571/1000000000000 : ℚ) : ℝ) ≤ stT183 161 := by
  have hc : ((991161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78114389571/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((991161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c162 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((300273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24723/78125) (δ := 2291/250000000) (ψ := -147111/1000000) 183 148
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t162 : ((117938702651/5000000000000 : ℚ) : ℝ) ≤ stT183 162 := by
  have hc : ((300223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117938702651/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((300223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c163 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-365977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5979953/10000000) (δ := 9239/1000000000) (ψ := -147111/1000000) 183 148
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t163 : ((-143337546261/2500000000000 : ℚ) : ℝ) ≤ stT183 163 := by
  have hc : ((-183001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143337546261/2500000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-183001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c164 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-932453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6929849/10000000) (δ := 2333/250000000) (ψ := -147111/1000000) 183 149
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t164 : ((-728162685107/10000000000000 : ℚ) : ℝ) ≤ stT183 164 := by
  have hc : ((-932503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-728162685107/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-932503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c165 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-8857/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2074353/5000000) (δ := 9171/1000000000) (ψ := -147111/1000000) 183 149
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t165 : ((-3449529069/500000000000 : ℚ) : ℝ) ≤ stT183 165 := by
  have hc : ((-4431/50000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3449529069/500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-4431/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c166 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((850563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692177/5000000) (δ := 577/62500000) (ψ := -147111/1000000) 183 149
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t166 : ((13202513299/200000000000 : ℚ) : ℝ) ≤ stT183 166 := by
  have hc : ((850513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13202513299/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((850513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c167 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((854933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1363437/10000000) (δ := 9171/1000000000) (ψ := -147111/1000000) 183 149
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t167 : ((661528127709/10000000000000 : ℚ) : ℝ) ≤ stT183 167 := by
  have hc : ((854883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((661528127709/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((854883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c168 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-67057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2047379/5000000) (δ := 9271/1000000000) (ψ := -147111/1000000) 183 149
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t168 : ((-51774191319/10000000000000 : ℚ) : ℝ) ≤ stT183 168 := by
  have hc : ((-67107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51774191319/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-67107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c169 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-114257/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6809929/10000000) (δ := 9271/1000000000) (ψ := -147111/1000000) 183 149
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t169 : ((-351579336243/5000000000000 : ℚ) : ℝ) ≤ stT183 169 := by
  have hc : ((-457053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351579336243/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-457053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c170 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-631/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3099461/5000000) (δ := 369/40000000) (ψ := -147111/1000000) 183 150
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t170 : ((-75622749/1250000000 : ℚ) : ℝ) ≤ stT183 170 := by
  have hc : ((-493/625 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75622749/1250000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-493/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c171 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((163799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3515639/10000000) (δ := 373/40000000) (ψ := -147111/1000000) 183 150
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t171 : ((125221971531/10000000000000 : ℚ) : ℝ) ≤ stT183 171 := by
  have hc : ((163749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125221971531/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((163749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c172 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((943021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424001/5000000) (δ := 369/40000000) (ψ := -147111/1000000) 183 150
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t172 : ((179751960933/2500000000000 : ℚ) : ℝ) ≤ stT183 172 := by
  have hc : ((942971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179751960933/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((942971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c173 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((150141/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1804171/10000000) (δ := 373/40000000) (ψ := -147111/1000000) 183 150
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t173 : ((22828469467/400000000000 : ℚ) : ℝ) ≤ stT183 173 := by
  have hc : ((150131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22828469467/400000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((150131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c174 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-204183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 555133/1250000) (δ := 369/40000000) (ψ := -147111/1000000) 183 150
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t174 : ((-154828833067/10000000000000 : ℚ) : ℝ) ≤ stT183 174 := by
  have hc : ((-204233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154828833067/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-204233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c175 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-475173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7062859/10000000) (δ := 373/40000000) (ψ := -147111/1000000) 183 150
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t175 : ((-179607974471/2500000000000 : ℚ) : ℝ) ≤ stT183 175 := by
  have hc : ((-237599/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179607974471/2500000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-237599/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c176 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-747647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6038269/10000000) (δ := 9217/1000000000) (ψ := -147111/1000000) 183 151
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t176 : ((-563598296963/10000000000000 : ℚ) : ℝ) ≤ stT183 176 := by
  have hc : ((-747697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563598296963/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-747697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c177 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((191147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -689233/2000000) (δ := 4643/500000000) (ψ := -147111/1000000) 183 151
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t177 : ((71818647831/5000000000000 : ℚ) : ℝ) ≤ stT183 177 := by
  have hc : ((191097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71818647831/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((191097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c178 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((470117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434351/5000000) (δ := 9217/1000000000) (ψ := -147111/1000000) 183 151
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t178 : ((88087131713/1250000000000 : ℚ) : ℝ) ≤ stT183 178 := by
  have hc : ((117523/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88087131713/1250000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((117523/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c179 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((48687/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33887/200000) (δ := 9317/1000000000) (ψ := -147111/1000000) 183 151
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t179 : ((58220851377/1000000000000 : ℚ) : ℝ) ≤ stT183 179 := by
  have hc : ((389471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58220851377/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((389471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c180 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-1261/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4243083/10000000) (δ := 4593/500000000) (ψ := -147111/1000000) 183 151
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t180 : ((-470133297/50000000000 : ℚ) : ℝ) ≤ stT183 180 := by
  have hc : ((-2523/20000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470133297/50000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-2523/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c181 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-227189/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1694431/2500000) (δ := 9317/1000000000) (ψ := -147111/1000000) 183 151
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t181 : ((-67551095577/1000000000000 : ℚ) : ℝ) ≤ stT183 181 := by
  have hc : ((-454403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67551095577/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-454403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c182 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-837691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6409597/10000000) (δ := 921/100000000) (ψ := -147111/1000000) 183 152
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t182 : ((-496780413/8000000000 : ℚ) : ℝ) ≤ stT183 182 := by
  have hc : ((-837741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-496780413/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-837741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c183 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((4853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1951363/5000000) (δ := 931/100000000) (ψ := -147111/1000000) 183 152
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t183 : ((892239747/1250000000000 : ℚ) : ℝ) ≤ stT183 183 := by
  have hc : ((1207/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((892239747/1250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((1207/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c184 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((845223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -704767/5000000) (δ := 931/100000000) (ψ := -147111/1000000) 183 152
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t184 : ((623069142157/10000000000000 : ℚ) : ℝ) ≤ stT183 184 := by
  have hc : ((845173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((623069142157/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((845173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c185 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((909771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 535081/5000000) (δ := 921/100000000) (ψ := -147111/1000000) 183 152
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t185 : ((334419807647/5000000000000 : ℚ) : ℝ) ≤ stT183 185 := by
  have hc : ((909721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334419807647/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((909721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c186 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((155581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3536453/10000000) (δ := 921/100000000) (ψ := -147111/1000000) 183 152
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t186 : ((22808154557/2000000000000 : ℚ) : ℝ) ≤ stT183 186 := by
  have hc : ((155531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22808154557/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((155531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c187 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-734569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93587/156250) (δ := 921/100000000) (ψ := -147111/1000000) 183 152
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t187 : ((-537207039987/10000000000000 : ℚ) : ℝ) ≤ stT183 187 := by
  have hc : ((-734619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537207039987/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-734619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c188 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-486807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727841/1000000) (δ := 93/10000000) (ψ := -147111/1000000) 183 153
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t188 : ((-887646871/12500000000 : ℚ) : ℝ) ≤ stT183 188 := by
  have hc : ((-30427/31250 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-887646871/12500000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-30427/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c189 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-45171/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4851327/10000000) (δ := 23/2500000) (ψ := -147111/1000000) 183 153
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t189 : ((-131446461637/5000000000000 : ℚ) : ℝ) ≤ stT183 189 := by
  have hc : ((-180709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131446461637/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-180709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c190 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((5613/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24371/100000) (δ := 9303/1000000000) (ψ := -147111/1000000) 183 153
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t190 : ((81434681/2000000000 : ℚ) : ℝ) ≤ stT183 190 := by
  have hc : ((449/800 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81434681/2000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((449/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c191 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((999899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35499/10000000) (δ := 23/2500000) (ψ := -147111/1000000) 183 153
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t191 : ((361732370163/5000000000000 : ℚ) : ℝ) ≤ stT183 191 := by
  have hc : ((999849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361732370163/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((999849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c192 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((11773/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29419/125000) (δ := 9203/1000000000) (ψ := -147111/1000000) 183 153
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t192 : ((2123924841/50000000000 : ℚ) : ℝ) ≤ stT183 192 := by
  have hc : ((2943/5000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2123924841/50000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((2943/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c193 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-157881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4730141/10000000) (δ := 9203/1000000000) (ψ := -147111/1000000) 183 153
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t193 : ((-7103954081/312500000000 : ℚ) : ℝ) ≤ stT183 193 := by
  have hc : ((-78953/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7103954081/312500000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-78953/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c194 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-954209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7094501/10000000) (δ := 9203/1000000000) (ψ := -147111/1000000) 183 153
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t194 : ((-685118837381/10000000000000 : ℚ) : ℝ) ≤ stT183 194 := by
  have hc : ((-954259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685118837381/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-954259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c195 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-401917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782659/1250000) (δ := 581/62500000) (ψ := -147111/1000000) 183 154
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t195 : ((-28783669533/500000000000 : ℚ) : ℝ) ≤ stT183 195 := by
  have hc : ((-200971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28783669533/500000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-200971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c196 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((2351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3921113/10000000) (δ := 9307/1000000000) (ψ := -147111/1000000) 183 154
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t196 : ((328713957/2000000000000 : ℚ) : ℝ) ≤ stT183 196 := by
  have hc : ((2301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328713957/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((2301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c197 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((4019/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31857/200000) (δ := 9207/1000000000) (ψ := -147111/1000000) 183 154
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t197 : ((45811821/800000000 : ℚ) : ℝ) ≤ stT183 197 := by
  have hc : ((643/800 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45811821/800000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((643/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c198 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((958403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72361/1000000) (δ := 9307/1000000000) (ψ := -147111/1000000) 183 154
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t198 : ((681071768157/10000000000000 : ℚ) : ℝ) ≤ stT183 198 := by
  have hc : ((958353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((681071768157/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((958353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c199 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((175873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3028403/10000000) (δ := 2299/250000000) (ψ := -147111/1000000) 183 154
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t199 : ((15581913261/625000000000 : ℚ) : ℝ) ≤ stT183 199 := by
  have hc : ((21981/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15581913261/625000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((21981/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c200 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-105873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2660811/5000000) (δ := 9207/1000000000) (ψ := -147111/1000000) 183 154
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t200 : ((-74870610481/2000000000000 : ℚ) : ℝ) ≤ stT183 200 := by
  have hc : ((-105883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74870610481/2000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-105883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c201 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-994983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7603449/10000000) (δ := 9207/1000000000) (ψ := -147111/1000000) 183 154
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t201 : ((-350921273209/5000000000000 : ℚ) : ℝ) ≤ stT183 201 := by
  have hc : ((-995033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350921273209/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-995033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c202 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-345487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5834079/10000000) (δ := 4607/500000000) (ψ := -147111/1000000) 183 155
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t202 : ((-15193847011/312500000000 : ℚ) : ℝ) ≤ stT183 202 := by
  have hc : ((-43189/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15193847011/312500000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-43189/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c203 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((17551/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3574807/10000000) (δ := 9189/1000000000) (ψ := -147111/1000000) 183 155
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t203 : ((24627986649/2500000000000 : ℚ) : ℝ) ≤ stT183 203 := by
  have hc : ((70179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24627986649/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((70179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c204 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((862473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -331663/2500000) (δ := 9189/1000000000) (ψ := -147111/1000000) 183 155
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t204 : ((30190841961/500000000000 : ℚ) : ℝ) ≤ stT183 204 := by
  have hc : ((862423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30190841961/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((862423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c205 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((467203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910523/10000000) (δ := 9189/1000000000) (ψ := -147111/1000000) 183 155
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t205 : ((16314556527/250000000000 : ℚ) : ℝ) ≤ stT183 205 := by
  have hc : ((233589/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16314556527/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((233589/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c206 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((77709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313681/1000000) (δ := 4657/500000000) (ψ := -147111/1000000) 183 155
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t206 : ((108267431069/5000000000000 : ℚ) : ℝ) ≤ stT183 206 := by
  have hc : ((155393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108267431069/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((155393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c207 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-67467/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5352299/10000000) (δ := 9189/1000000000) (ψ := -147111/1000000) 183 155
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t207 : ((-187588859757/5000000000000 : ℚ) : ℝ) ≤ stT183 207 := by
  have hc : ((-269893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187588859757/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-269893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c208 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-992959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7557129/10000000) (δ := 4607/500000000) (ψ := -147111/1000000) 183 155
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t208 : ((-5379129753/78125000000 : ℚ) : ℝ) ≤ stT183 208 := by
  have hc : ((-993009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5379129753/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-993009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c209 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-14511/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5956573/10000000) (δ := 9181/1000000000) (ψ := -147111/1000000) 183 156
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t209 : ((-125477101/2500000000 : ℚ) : ℝ) ≤ stT183 209 := by
  have hc : ((-907/1250 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125477101/2500000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-907/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c210 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((30821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -943197/2500000) (δ := 4611/500000000) (ψ := -147111/1000000) 183 156
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t210 : ((1062562087/250000000000 : ℚ) : ℝ) ≤ stT183 210 := by
  have hc : ((7699/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1062562087/250000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((7699/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c211 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((401121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1599389/10000000) (δ := 9281/1000000000) (ψ := -147111/1000000) 183 156
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t211 : ((8628928659/156250000000 : ℚ) : ℝ) ≤ stT183 211 := by
  have hc : ((50137/62500 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8628928659/156250000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((50137/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c212 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((194937/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 563717/10000000) (δ := 9181/1000000000) (ψ := -147111/1000000) 183 156
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t212 : ((66938126727/1000000000000 : ℚ) : ℝ) ≤ stT183 212 := by
  have hc : ((194927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66938126727/1000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((194927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c213 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((232719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1358333/5000000) (δ := 9281/1000000000) (ψ := -147111/1000000) 183 156
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t213 : ((19929892059/625000000000 : ℚ) : ℝ) ≤ stT183 213 := by
  have hc : ((116347/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19929892059/625000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((116347/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c214 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-364433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4859551/10000000) (δ := 4661/500000000) (ψ := -147111/1000000) 183 156
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t214 : ((-124577738019/5000000000000 : ℚ) : ℝ) ≤ stT183 214 := by
  have hc : ((-364483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124577738019/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-364483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c215 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-470601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 218513/312500) (δ := 4661/500000000) (ψ := -147111/1000000) 183 156
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t215 : ((-32096457887/500000000000 : ℚ) : ℝ) ≤ stT183 215 := by
  have hc : ((-235313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32096457887/500000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-235313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c216 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-109423/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1318513/2000000) (δ := 4637/500000000) (ψ := -147111/1000000) 183 157
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t216 : ((-148914387419/2500000000000 : ℚ) : ℝ) ≤ stT183 216 := by
  have hc : ((-437717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148914387419/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-437717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c217 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-219177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2239709/5000000) (δ := 4587/500000000) (ψ := -147111/1000000) 183 157
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t217 : ((-29764230563/2000000000000 : ℚ) : ℝ) ≤ stT183 217 := by
  have hc : ((-219227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29764230563/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-219227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c218 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((581367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237597/1000000) (δ := 9229/1000000000) (ψ := -147111/1000000) 183 157
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t218 : ((78743456869/2000000000000 : ℚ) : ℝ) ≤ stT183 218 := by
  have hc : ((581317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78743456869/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((581317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c219 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((993639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28213/1000000) (δ := 4587/500000000) (ψ := -147111/1000000) 183 157
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t219 : ((671404850093/10000000000000 : ℚ) : ℝ) ≤ stT183 219 := by
  have hc : ((993589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671404850093/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((993589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c220 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((751239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1802149/10000000) (δ := 9329/1000000000) (ψ := -147111/1000000) 183 157
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t220 : ((506450872611/10000000000000 : ℚ) : ℝ) ≤ stT183 220 := by
  have hc : ((751189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506450872611/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((751189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c221 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((9997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3877003/10000000) (δ := 9329/1000000000) (ψ := -147111/1000000) 183 157
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t221 : ((52405353/39062500000 : ℚ) : ℝ) ≤ stT183 221 := by
  have hc : ((2493/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52405353/39062500000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((2493/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c222 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-360823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185701/312500) (δ := 4587/500000000) (ψ := -147111/1000000) 183 157
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t222 : ((-15136603821/312500000000 : ℚ) : ℝ) ≤ stT183 222 := by
  have hc : ((-22553/31250 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15136603821/312500000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-22553/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c223 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-998327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7709343/10000000) (δ := 2309/250000000) (ψ := -147111/1000000) 183 158
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t223 : ((-13371263161/200000000000 : ℚ) : ℝ) ≤ stT183 223 := by
  have hc : ((-998377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13371263161/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-998377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c224 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-39983/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5662351/10000000) (δ := 9167/1000000000) (ψ := -147111/1000000) 183 158
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t224 : ((-106867557453/2500000000000 : ℚ) : ℝ) ≤ stT183 224 := by
  have hc : ((-319889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106867557453/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-319889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c225 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((30179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3624463/10000000) (δ := 9167/1000000000) (ψ := -147111/1000000) 183 158
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t225 : ((20110979889/2500000000000 : ℚ) : ℝ) ≤ stT183 225 := by
  have hc : ((60333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20110979889/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((60333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c226 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((200783/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199457/1250000) (δ := 4609/250000000) (ψ := -147111/1000000) 183 158
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t226 : ((26710105779/500000000000 : ℚ) : ℝ) ≤ stT183 226 := by
  have hc : ((401541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26710105779/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((401541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c227 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((985637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 424229/10000000) (δ := 9167/1000000000) (ψ := -147111/1000000) 183 158
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t227 : ((654156760401/10000000000000 : ℚ) : ℝ) ≤ stT183 227 := by
  have hc : ((985587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((654156760401/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((985587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c228 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((140481/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152201/625000) (δ := 9167/1000000000) (ψ := -147111/1000000) 183 158
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t228 : ((93027511621/2500000000000 : ℚ) : ℝ) ≤ stT183 228 := by
  have hc : ((280937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93027511621/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((280937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c229 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-50689/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4437419/10000000) (δ := 9167/1000000000) (ψ := -147111/1000000) 183 158
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t229 : ((-67009029057/5000000000000 : ℚ) : ℝ) ≤ stT183 229 := by
  have hc : ((-101403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67009029057/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-101403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c230 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-842311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1607721/2500000) (δ := 2309/250000000) (ψ := -147111/1000000) 183 158
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t230 : ((-555436838541/10000000000000 : ℚ) : ℝ) ≤ stT183 230 := by
  have hc : ((-842361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-555436838541/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-842361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c231 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-60929/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7292261/10000000) (δ := 9343/1000000000) (ψ := -147111/1000000) 183 159
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t231 : ((-10022603377/156250000000 : ℚ) : ℝ) ≤ stT183 231 := by
  have hc : ((-487457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10022603377/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-487457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c232 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-527471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1329011/2500000) (δ := 9343/1000000000) (ψ := -147111/1000000) 183 159
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t232 : ((-346334944693/10000000000000 : ℚ) : ℝ) ≤ stT183 232 := by
  have hc : ((-527521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346334944693/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-527521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c233 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((114709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3348291/10000000) (δ := 9243/1000000000) (ψ := -147111/1000000) 183 159
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t233 : ((18782974191/1250000000000 : ℚ) : ℝ) ≤ stT183 233 := by
  have hc : ((28671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18782974191/1250000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((28671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c234 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((849593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347239/2500000) (δ := 229/25000000) (ψ := -147111/1000000) 183 159
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t234 : ((13884081249/250000000000 : ℚ) : ℝ) ≤ stT183 234 := by
  have hc : ((849543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13884081249/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((849543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c235 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((487419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 562007/10000000) (δ := 229/25000000) (ψ := -147111/1000000) 183 159
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t235 : ((19871297077/312500000000 : ℚ) : ℝ) ≤ stT183 235 := by
  have hc : ((243697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19871297077/312500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((243697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c236 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((538723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2504689/10000000) (δ := 463/50000000) (ψ := -147111/1000000) 183 159
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t236 : ((5478843083/156250000000 : ℚ) : ℝ) ≤ stT183 236 := by
  have hc : ((538673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5478843083/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((538673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c237 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-203429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4439137/10000000) (δ := 9343/1000000000) (ψ := -147111/1000000) 183 159
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t237 : ((-13217385403/1000000000000 : ℚ) : ℝ) ≤ stT183 237 := by
  have hc : ((-203479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13217385403/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-203479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c238 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-165583/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9946/15625) (δ := 463/50000000) (ψ := -147111/1000000) 183 159
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t238 : ((-26834511243/500000000000 : ℚ) : ℝ) ≤ stT183 238 := by
  have hc : ((-165593/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26834511243/500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-165593/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c239 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-61579/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7424271/10000000) (δ := 37/4000000) (ψ := -147111/1000000) 183 160
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t239 : ((-318673702479/5000000000000 : ℚ) : ℝ) ≤ stT183 239 := by
  have hc : ((-492657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318673702479/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-492657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c240 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-148257/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2757013/5000000) (δ := 9253/1000000000) (ψ := -147111/1000000) 183 160
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t240 : ((-95707665711/2500000000000 : ℚ) : ℝ) ≤ stT183 240 := by
  have hc : ((-296539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95707665711/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-296539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c241 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((62883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3611741/10000000) (δ := 9253/1000000000) (ψ := -147111/1000000) 183 160
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t241 : ((5061294731/625000000000 : ℚ) : ℝ) ≤ stT183 241 := by
  have hc : ((31429/250000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5061294731/625000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((31429/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c242 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((773197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68693/400000) (δ := 9253/1000000000) (ψ := -147111/1000000) 183 160
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t242 : ((62124680891/1250000000000 : ℚ) : ℝ) ≤ stT183 242 := by
  have hc : ((773147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62124680891/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((773147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c243 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((997709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42317/2500000) (δ := 9153/1000000000) (ψ := -147111/1000000) 183 160
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t243 : ((1279996497/20000000000 : ℚ) : ℝ) ≤ stT183 243 := by
  have hc : ((997659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1279996497/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((997659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c244 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((42673/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2048129/10000000) (δ := 9153/1000000000) (ψ := -147111/1000000) 183 160
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t244 : ((27316571257/625000000000 : ℚ) : ℝ) ≤ stT183 244 := by
  have hc : ((341359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27316571257/625000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((341359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c245 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((771/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3919281/10000000) (δ := 18353/1000000000) (ψ := -147111/1000000) 183 160
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t245 : ((242293723/1250000000000 : ℚ) : ℝ) ≤ stT183 245 := by
  have hc : ((1517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242293723/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((1517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c246 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-338007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5782839/10000000) (δ := 37/4000000) (ψ := -147111/1000000) 183 160
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t246 : ((-13470089279/312500000000 : ℚ) : ℝ) ≤ stT183 246 := by
  have hc : ((-21127/31250 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13470089279/312500000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-21127/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c247 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-996299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 305553/400000) (δ := 37/4000000) (ψ := -147111/1000000) 183 160
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t247 : ((-126792384693/2000000000000 : ℚ) : ℝ) ≤ stT183 247 := by
  have hc : ((-996349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126792384693/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-996349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c248 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-49629/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388791/625000) (δ := 4673/500000000) (ψ := -147111/1000000) 183 161
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t248 : ((-252131592057/5000000000000 : ℚ) : ℝ) ≤ stT183 248 := by
  have hc : ((-397057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252131592057/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-397057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c249 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-45017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -437963/1000000) (δ := 4623/500000000) (ψ := -147111/1000000) 183 161
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t249 : ((-2282905591/200000000000 : ℚ) : ℝ) ≤ stT183 249 := by
  have hc : ((-90059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2282905591/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-90059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_c250 :
    |Real.cos (((183 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((104951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636481/2500000) (δ := 9157/1000000000) (ψ := -147111/1000000) 183 161
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st183_t250 : ((13274092031/400000000000 : ℚ) : ℝ) ≤ stT183 250 := by
  have hc : ((104941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((183 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st183_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13274092031/400000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((104941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st183_p1 : ((989149/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT183 (i+1) := by
  rw [Finset.sum_range_one]
  exact st183_t1

theorem st183_p2 : ((5790999135979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT183 (i+1))
      = (∑ i ∈ Finset.range 1, stT183 (i+1)) + stT183 2 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 1
    simpa using h
  have hprev := st183_p1
  have hstep := st183_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p3 : ((4326394200041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT183 (i+1))
      = (∑ i ∈ Finset.range 2, stT183 (i+1)) + stT183 3 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 2
    simpa using h
  have hprev := st183_p2
  have hstep := st183_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p4 : ((13265270992103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT183 (i+1))
      = (∑ i ∈ Finset.range 3, stT183 (i+1)) + stT183 4 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 3
    simpa using h
  have hprev := st183_p3
  have hstep := st183_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p5 : ((8432117524879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT183 (i+1))
      = (∑ i ∈ Finset.range 4, stT183 (i+1)) + stT183 5 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 4
    simpa using h
  have hprev := st183_p4
  have hstep := st183_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p6 : ((447576687549/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT183 (i+1))
      = (∑ i ∈ Finset.range 5, stT183 (i+1)) + stT183 6 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 5
    simpa using h
  have hprev := st183_p5
  have hstep := st183_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p7 : ((3341281087489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT183 (i+1))
      = (∑ i ∈ Finset.range 6, stT183 (i+1)) + stT183 7 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 6
    simpa using h
  have hprev := st183_p6
  have hstep := st183_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p8 : ((13696177543631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT183 (i+1))
      = (∑ i ∈ Finset.range 7, stT183 (i+1)) + stT183 8 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 7
    simpa using h
  have hprev := st183_p7
  have hstep := st183_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p9 : ((4251798469799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT183 (i+1))
      = (∑ i ∈ Finset.range 8, stT183 (i+1)) + stT183 9 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 8
    simpa using h
  have hprev := st183_p8
  have hstep := st183_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p10 : ((38492767677/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT183 (i+1))
      = (∑ i ∈ Finset.range 9, stT183 (i+1)) + stT183 10 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 9
    simpa using h
  have hprev := st183_p9
  have hstep := st183_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p11 : ((4334593157443/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT183 (i+1))
      = (∑ i ∈ Finset.range 10, stT183 (i+1)) + stT183 11 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 10
    simpa using h
  have hprev := st183_p10
  have hstep := st183_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p12 : ((19367594093007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT183 (i+1))
      = (∑ i ∈ Finset.range 11, stT183 (i+1)) + stT183 12 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 11
    simpa using h
  have hprev := st183_p11
  have hstep := st183_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p13 : ((18993454355109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT183 (i+1))
      = (∑ i ∈ Finset.range 12, stT183 (i+1)) + stT183 13 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 12
    simpa using h
  have hprev := st183_p12
  have hstep := st183_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p14 : ((21018973537669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT183 (i+1))
      = (∑ i ∈ Finset.range 13, stT183 (i+1)) + stT183 14 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 13
    simpa using h
  have hprev := st183_p13
  have hstep := st183_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p15 : ((4614448021789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT183 (i+1))
      = (∑ i ∈ Finset.range 14, stT183 (i+1)) + stT183 15 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 14
    simpa using h
  have hprev := st183_p14
  have hstep := st183_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p16 : ((4695877521789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT183 (i+1))
      = (∑ i ∈ Finset.range 15, stT183 (i+1)) + stT183 16 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 15
    simpa using h
  have hprev := st183_p15
  have hstep := st183_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p17 : ((1321056717687/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT183 (i+1))
      = (∑ i ∈ Finset.range 16, stT183 (i+1)) + stT183 17 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 16
    simpa using h
  have hprev := st183_p16
  have hstep := st183_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p18 : ((68039982207/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT183 (i+1))
      = (∑ i ∈ Finset.range 17, stT183 (i+1)) + stT183 18 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 17
    simpa using h
  have hprev := st183_p17
  have hstep := st183_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p19 : ((2222013197967/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT183 (i+1))
      = (∑ i ∈ Finset.range 18, stT183 (i+1)) + stT183 19 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 18
    simpa using h
  have hprev := st183_p18
  have hstep := st183_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p20 : ((10933879483911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT183 (i+1))
      = (∑ i ∈ Finset.range 19, stT183 (i+1)) + stT183 20 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 19
    simpa using h
  have hprev := st183_p19
  have hstep := st183_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p21 : ((21144085128231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT183 (i+1))
      = (∑ i ∈ Finset.range 20, stT183 (i+1)) + stT183 21 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 20
    simpa using h
  have hprev := st183_p20
  have hstep := st183_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p22 : ((579173707347/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT183 (i+1))
      = (∑ i ∈ Finset.range 21, stT183 (i+1)) + stT183 22 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 21
    simpa using h
  have hprev := st183_p21
  have hstep := st183_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p23 : ((879448646853/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT183 (i+1))
      = (∑ i ∈ Finset.range 22, stT183 (i+1)) + stT183 23 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 22
    simpa using h
  have hprev := st183_p22
  have hstep := st183_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p24 : ((20231476774719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT183 (i+1))
      = (∑ i ∈ Finset.range 23, stT183 (i+1)) + stT183 24 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 23
    simpa using h
  have hprev := st183_p23
  have hstep := st183_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p25 : ((20535728774719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT183 (i+1))
      = (∑ i ∈ Finset.range 24, stT183 (i+1)) + stT183 25 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 24
    simpa using h
  have hprev := st183_p24
  have hstep := st183_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p26 : ((11116912760831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT183 (i+1))
      = (∑ i ∈ Finset.range 25, stT183 (i+1)) + stT183 26 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 25
    simpa using h
  have hprev := st183_p25
  have hstep := st183_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p27 : ((12074358246581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT183 (i+1))
      = (∑ i ∈ Finset.range 26, stT183 (i+1)) + stT183 27 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 26
    simpa using h
  have hprev := st183_p26
  have hstep := st183_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p28 : ((6458045789879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT183 (i+1))
      = (∑ i ∈ Finset.range 27, stT183 (i+1)) + stT183 28 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 27
    simpa using h
  have hprev := st183_p27
  have hstep := st183_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p29 : ((13677020781427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT183 (i+1))
      = (∑ i ∈ Finset.range 28, stT183 (i+1)) + stT183 29 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 28
    simpa using h
  have hprev := st183_p28
  have hstep := st183_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p30 : ((5785679622061/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT183 (i+1))
      = (∑ i ∈ Finset.range 29, stT183 (i+1)) + stT183 30 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 29
    simpa using h
  have hprev := st183_p29
  have hstep := st183_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p31 : ((1533465165147/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT183 (i+1))
      = (∑ i ∈ Finset.range 30, stT183 (i+1)) + stT183 31 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 30
    simpa using h
  have hprev := st183_p30
  have hstep := st183_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p32 : ((16196226328433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT183 (i+1))
      = (∑ i ∈ Finset.range 31, stT183 (i+1)) + stT183 32 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 31
    simpa using h
  have hprev := st183_p31
  have hstep := st183_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p33 : ((16752822917061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT183 (i+1))
      = (∑ i ∈ Finset.range 32, stT183 (i+1)) + stT183 33 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 32
    simpa using h
  have hprev := st183_p32
  have hstep := st183_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p34 : ((16644852543459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT183 (i+1))
      = (∑ i ∈ Finset.range 33, stT183 (i+1)) + stT183 34 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 33
    simpa using h
  have hprev := st183_p33
  have hstep := st183_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p35 : ((6355927761303/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT183 (i+1))
      = (∑ i ∈ Finset.range 34, stT183 (i+1)) + stT183 35 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 34
    simpa using h
  have hprev := st183_p34
  have hstep := st183_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p36 : ((30464728543533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT183 (i+1))
      = (∑ i ∈ Finset.range 35, stT183 (i+1)) + stT183 36 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 35
    simpa using h
  have hprev := st183_p35
  have hstep := st183_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p37 : ((31044024235441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT183 (i+1))
      = (∑ i ∈ Finset.range 36, stT183 (i+1)) + stT183 37 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 36
    simpa using h
  have hprev := st183_p36
  have hstep := st183_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p38 : ((32636266209577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT183 (i+1))
      = (∑ i ∈ Finset.range 37, stT183 (i+1)) + stT183 38 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 37
    simpa using h
  have hprev := st183_p37
  have hstep := st183_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p39 : ((32395090722429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT183 (i+1))
      = (∑ i ∈ Finset.range 38, stT183 (i+1)) + stT183 39 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 38
    simpa using h
  have hprev := st183_p38
  have hstep := st183_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p40 : ((30855643195581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT183 (i+1))
      = (∑ i ∈ Finset.range 39, stT183 (i+1)) + stT183 40 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 39
    simpa using h
  have hprev := st183_p39
  have hstep := st183_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p41 : ((6299619613749/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT183 (i+1))
      = (∑ i ∈ Finset.range 40, stT183 (i+1)) + stT183 41 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 40
    simpa using h
  have hprev := st183_p40
  have hstep := st183_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p42 : ((32651401051803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT183 (i+1))
      = (∑ i ∈ Finset.range 41, stT183 (i+1)) + stT183 42 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 41
    simpa using h
  have hprev := st183_p41
  have hstep := st183_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p43 : ((31270260881239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT183 (i+1))
      = (∑ i ∈ Finset.range 42, stT183 (i+1)) + stT183 43 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 42
    simpa using h
  have hprev := st183_p42
  have hstep := st183_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p44 : ((31371662112911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT183 (i+1))
      = (∑ i ∈ Finset.range 43, stT183 (i+1)) + stT183 44 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 43
    simpa using h
  have hprev := st183_p43
  have hstep := st183_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p45 : ((3254259920559/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT183 (i+1))
      = (∑ i ∈ Finset.range 44, stT183 (i+1)) + stT183 45 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 44
    simpa using h
  have hprev := st183_p44
  have hstep := st183_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p46 : ((3110152468831/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT183 (i+1))
      = (∑ i ∈ Finset.range 45, stT183 (i+1)) + stT183 46 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 45
    simpa using h
  have hprev := st183_p45
  have hstep := st183_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p47 : ((31880488472429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT183 (i+1))
      = (∑ i ∈ Finset.range 46, stT183 (i+1)) + stT183 47 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 46
    simpa using h
  have hprev := st183_p46
  have hstep := st183_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p48 : ((4011614287663/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT183 (i+1))
      = (∑ i ∈ Finset.range 47, stT183 (i+1)) + stT183 48 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 47
    simpa using h
  have hprev := st183_p47
  have hstep := st183_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p49 : ((3886085666023/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT183 (i+1))
      = (∑ i ∈ Finset.range 48, stT183 (i+1)) + stT183 49 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 48
    simpa using h
  have hprev := st183_p48
  have hstep := st183_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p50 : ((32463694929611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT183 (i+1))
      = (∑ i ∈ Finset.range 49, stT183 (i+1)) + stT183 50 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 49
    simpa using h
  have hprev := st183_p49
  have hstep := st183_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p51 : ((15552833704393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT183 (i+1))
      = (∑ i ∈ Finset.range 50, stT183 (i+1)) + stT183 51 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 50
    simpa using h
  have hprev := st183_p50
  have hstep := st183_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p52 : ((16101236472643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT183 (i+1))
      = (∑ i ∈ Finset.range 51, stT183 (i+1)) + stT183 52 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 51
    simpa using h
  have hprev := st183_p51
  have hstep := st183_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p53 : ((3932911278461/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT183 (i+1))
      = (∑ i ∈ Finset.range 52, stT183 (i+1)) + stT183 53 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 52
    simpa using h
  have hprev := st183_p52
  have hstep := st183_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p54 : ((3981397544471/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT183 (i+1))
      = (∑ i ∈ Finset.range 53, stT183 (i+1)) + stT183 54 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 53
    simpa using h
  have hprev := st183_p53
  have hstep := st183_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p55 : ((3969128284321/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT183 (i+1))
      = (∑ i ∈ Finset.range 54, stT183 (i+1)) + stT183 55 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 54
    simpa using h
  have hprev := st183_p54
  have hstep := st183_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p56 : ((7910548242997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT183 (i+1))
      = (∑ i ∈ Finset.range 55, stT183 (i+1)) + stT183 56 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 55
    simpa using h
  have hprev := st183_p55
  have hstep := st183_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p57 : ((3984975592633/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT183 (i+1))
      = (∑ i ∈ Finset.range 56, stT183 (i+1)) + stT183 57 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 56
    simpa using h
  have hprev := st183_p56
  have hstep := st183_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p58 : ((31591233759079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT183 (i+1))
      = (∑ i ∈ Finset.range 57, stT183 (i+1)) + stT183 58 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 57
    simpa using h
  have hprev := st183_p57
  have hstep := st183_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p59 : ((31860279536041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT183 (i+1))
      = (∑ i ∈ Finset.range 58, stT183 (i+1)) + stT183 59 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 58
    simpa using h
  have hprev := st183_p58
  have hstep := st183_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p60 : ((31677105419471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT183 (i+1))
      = (∑ i ∈ Finset.range 59, stT183 (i+1)) + stT183 60 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 59
    simpa using h
  have hprev := st183_p59
  have hstep := st183_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p61 : ((31709795775247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT183 (i+1))
      = (∑ i ∈ Finset.range 60, stT183 (i+1)) + stT183 61 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 60
    simpa using h
  have hprev := st183_p60
  have hstep := st183_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p62 : ((31887374935073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT183 (i+1))
      = (∑ i ∈ Finset.range 61, stT183 (i+1)) + stT183 62 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 61
    simpa using h
  have hprev := st183_p61
  have hstep := st183_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p63 : ((31450741409979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT183 (i+1))
      = (∑ i ∈ Finset.range 62, stT183 (i+1)) + stT183 63 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 62
    simpa using h
  have hprev := st183_p62
  have hstep := st183_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p64 : ((32170355159979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT183 (i+1))
      = (∑ i ∈ Finset.range 63, stT183 (i+1)) + stT183 64 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 63
    simpa using h
  have hprev := st183_p63
  have hstep := st183_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p65 : ((31185100850703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT183 (i+1))
      = (∑ i ∈ Finset.range 64, stT183 (i+1)) + stT183 65 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 64
    simpa using h
  have hprev := st183_p64
  have hstep := st183_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p66 : ((32359023532503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT183 (i+1))
      = (∑ i ∈ Finset.range 65, stT183 (i+1)) + stT183 66 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 65
    simpa using h
  have hprev := st183_p65
  have hstep := st183_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p67 : ((31141609351783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT183 (i+1))
      = (∑ i ∈ Finset.range 66, stT183 (i+1)) + stT183 67 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 66
    simpa using h
  have hprev := st183_p66
  have hstep := st183_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p68 : ((6439414912637/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT183 (i+1))
      = (∑ i ∈ Finset.range 67, stT183 (i+1)) + stT183 68 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 67
    simpa using h
  have hprev := st183_p67
  have hstep := st183_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p69 : ((6306244030057/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT183 (i+1))
      = (∑ i ∈ Finset.range 68, stT183 (i+1)) + stT183 69 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 68
    simpa using h
  have hprev := st183_p68
  have hstep := st183_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p70 : ((31623769044781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT183 (i+1))
      = (∑ i ∈ Finset.range 69, stT183 (i+1)) + stT183 70 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 69
    simpa using h
  have hprev := st183_p69
  have hstep := st183_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p71 : ((32159334827337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT183 (i+1))
      = (∑ i ∈ Finset.range 70, stT183 (i+1)) + stT183 71 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 70
    simpa using h
  have hprev := st183_p70
  have hstep := st183_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p72 : ((31136801247561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT183 (i+1))
      = (∑ i ∈ Finset.range 71, stT183 (i+1)) + stT183 72 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 71
    simpa using h
  have hprev := st183_p71
  have hstep := st183_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p73 : ((32301655136133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT183 (i+1))
      = (∑ i ∈ Finset.range 72, stT183 (i+1)) + stT183 73 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 72
    simpa using h
  have hprev := st183_p72
  have hstep := st183_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p74 : ((31450029135841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT183 (i+1))
      = (∑ i ∈ Finset.range 73, stT183 (i+1)) + stT183 74 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 73
    simpa using h
  have hprev := st183_p73
  have hstep := st183_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p75 : ((31607545226941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT183 (i+1))
      = (∑ i ∈ Finset.range 74, stT183 (i+1)) + stT183 75 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 74
    simpa using h
  have hprev := st183_p74
  have hstep := st183_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p76 : ((32236911366123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT183 (i+1))
      = (∑ i ∈ Finset.range 75, stT183 (i+1)) + stT183 76 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 75
    simpa using h
  have hprev := st183_p75
  have hstep := st183_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p77 : ((6226013123961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT183 (i+1))
      = (∑ i ∈ Finset.range 76, stT183 (i+1)) + stT183 77 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 76
    simpa using h
  have hprev := st183_p76
  have hstep := st183_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p78 : ((8025336321363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT183 (i+1))
      = (∑ i ∈ Finset.range 77, stT183 (i+1)) + stT183 78 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 77
    simpa using h
  have hprev := st183_p77
  have hstep := st183_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p79 : ((1592747606927/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT183 (i+1))
      = (∑ i ∈ Finset.range 78, stT183 (i+1)) + stT183 79 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 78
    simpa using h
  have hprev := st183_p78
  have hstep := st183_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p80 : ((3900781085891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT183 (i+1))
      = (∑ i ∈ Finset.range 79, stT183 (i+1)) + stT183 80 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 79
    simpa using h
  have hprev := st183_p79
  have hstep := st183_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p81 : ((32313425243077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT183 (i+1))
      = (∑ i ∈ Finset.range 80, stT183 (i+1)) + stT183 81 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 80
    simpa using h
  have hprev := st183_p80
  have hstep := st183_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p82 : ((31554010320513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT183 (i+1))
      = (∑ i ∈ Finset.range 81, stT183 (i+1)) + stT183 82 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 81
    simpa using h
  have hprev := st183_p81
  have hstep := st183_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p83 : ((3921686631297/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT183 (i+1))
      = (∑ i ∈ Finset.range 82, stT183 (i+1)) + stT183 83 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 82
    simpa using h
  have hprev := st183_p82
  have hstep := st183_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p84 : ((126379667799/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT183 (i+1))
      = (∑ i ∈ Finset.range 83, stT183 (i+1)) + stT183 84 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 83
    simpa using h
  have hprev := st183_p83
  have hstep := st183_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p85 : ((15705984980673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT183 (i+1))
      = (∑ i ∈ Finset.range 84, stT183 (i+1)) + stT183 85 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 84
    simpa using h
  have hprev := st183_p84
  have hstep := st183_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p86 : ((7866281253121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT183 (i+1))
      = (∑ i ∈ Finset.range 85, stT183 (i+1)) + stT183 86 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 85
    simpa using h
  have hprev := st183_p85
  have hstep := st183_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p87 : ((8088353172241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT183 (i+1))
      = (∑ i ∈ Finset.range 86, stT183 (i+1)) + stT183 87 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 86
    simpa using h
  have hprev := st183_p86
  have hstep := st183_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p88 : ((3924530562419/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT183 (i+1))
      = (∑ i ∈ Finset.range 87, stT183 (i+1)) + stT183 88 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 87
    simpa using h
  have hprev := st183_p87
  have hstep := st183_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p89 : ((31439728756283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT183 (i+1))
      = (∑ i ∈ Finset.range 88, stT183 (i+1)) + stT183 89 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 88
    simpa using h
  have hprev := st183_p88
  have hstep := st183_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p90 : ((32357043886547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT183 (i+1))
      = (∑ i ∈ Finset.range 89, stT183 (i+1)) + stT183 90 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 89
    simpa using h
  have hprev := st183_p89
  have hstep := st183_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p91 : ((31494458381157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT183 (i+1))
      = (∑ i ∈ Finset.range 90, stT183 (i+1)) + stT183 91 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 90
    simpa using h
  have hprev := st183_p90
  have hstep := st183_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p92 : ((15656315261119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT183 (i+1))
      = (∑ i ∈ Finset.range 91, stT183 (i+1)) + stT183 92 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 91
    simpa using h
  have hprev := st183_p91
  have hstep := st183_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p93 : ((4040208090927/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT183 (i+1))
      = (∑ i ∈ Finset.range 92, stT183 (i+1)) + stT183 93 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 92
    simpa using h
  have hprev := st183_p92
  have hstep := st183_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p94 : ((634466674619/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT183 (i+1))
      = (∑ i ∈ Finset.range 93, stT183 (i+1)) + stT183 94 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 93
    simpa using h
  have hprev := st183_p93
  have hstep := st183_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p95 : ((15577823619251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT183 (i+1))
      = (∑ i ∈ Finset.range 94, stT183 (i+1)) + stT183 95 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 94
    simpa using h
  have hprev := st183_p94
  have hstep := st183_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p96 : ((16073381577771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT183 (i+1))
      = (∑ i ∈ Finset.range 95, stT183 (i+1)) + stT183 96 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 95
    simpa using h
  have hprev := st183_p95
  have hstep := st183_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p97 : ((6412148388471/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT183 (i+1))
      = (∑ i ∈ Finset.range 96, stT183 (i+1)) + stT183 97 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 96
    simpa using h
  have hprev := st183_p96
  have hstep := st183_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p98 : ((1245069775081/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT183 (i+1))
      = (∑ i ∈ Finset.range 97, stT183 (i+1)) + stT183 98 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 97
    simpa using h
  have hprev := st183_p97
  have hstep := st183_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p99 : ((15878548274083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT183 (i+1))
      = (∑ i ∈ Finset.range 98, stT183 (i+1)) + stT183 99 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 98
    simpa using h
  have hprev := st183_p98
  have hstep := st183_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p100 : ((16170819981811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT183 (i+1))
      = (∑ i ∈ Finset.range 99, stT183 (i+1)) + stT183 100 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 99
    simpa using h
  have hprev := st183_p99
  have hstep := st183_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p101 : ((7853856936761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT183 (i+1))
      = (∑ i ∈ Finset.range 100, stT183 (i+1)) + stT183 101 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 100
    simpa using h
  have hprev := st183_p100
  have hstep := st183_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p102 : ((7818793320711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT183 (i+1))
      = (∑ i ∈ Finset.range 101, stT183 (i+1)) + stT183 102 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 101
    simpa using h
  have hprev := st183_p101
  have hstep := st183_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p103 : ((806446638561/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT183 (i+1))
      = (∑ i ∈ Finset.range 102, stT183 (i+1)) + stT183 103 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 102
    simpa using h
  have hprev := st183_p102
  have hstep := st183_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p104 : ((31996431861449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT183 (i+1))
      = (∑ i ∈ Finset.range 103, stT183 (i+1)) + stT183 104 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 103
    simpa using h
  have hprev := st183_p103
  have hstep := st183_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p105 : ((31117740360059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT183 (i+1))
      = (∑ i ∈ Finset.range 104, stT183 (i+1)) + stT183 105 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 104
    simpa using h
  have hprev := st183_p104
  have hstep := st183_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p106 : ((31677330672249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT183 (i+1))
      = (∑ i ∈ Finset.range 105, stT183 (i+1)) + stT183 106 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 105
    simpa using h
  have hprev := st183_p105
  have hstep := st183_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p107 : ((1295077952593/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT183 (i+1))
      = (∑ i ∈ Finset.range 106, stT183 (i+1)) + stT183 107 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 106
    simpa using h
  have hprev := st183_p106
  have hstep := st183_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p108 : ((15813634822743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT183 (i+1))
      = (∑ i ∈ Finset.range 107, stT183 (i+1)) + stT183 108 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 107
    simpa using h
  have hprev := st183_p107
  have hstep := st183_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p109 : ((15558479288213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT183 (i+1))
      = (∑ i ∈ Finset.range 108, stT183 (i+1)) + stT183 109 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 108
    simpa using h
  have hprev := st183_p108
  have hstep := st183_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p110 : ((999083805531/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT183 (i+1))
      = (∑ i ∈ Finset.range 109, stT183 (i+1)) + stT183 110 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 109
    simpa using h
  have hprev := st183_p109
  have hstep := st183_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p111 : ((32319199888351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT183 (i+1))
      = (∑ i ∈ Finset.range 110, stT183 (i+1)) + stT183 111 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 110
    simpa using h
  have hprev := st183_p110
  have hstep := st183_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p112 : ((1256720623239/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT183 (i+1))
      = (∑ i ∈ Finset.range 111, stT183 (i+1)) + stT183 112 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 111
    simpa using h
  have hprev := st183_p111
  have hstep := st183_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p113 : ((31185514504383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT183 (i+1))
      = (∑ i ∈ Finset.range 112, stT183 (i+1)) + stT183 113 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 112
    simpa using h
  have hprev := st183_p112
  have hstep := st183_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p114 : ((32101837424493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT183 (i+1))
      = (∑ i ∈ Finset.range 113, stT183 (i+1)) + stT183 114 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 113
    simpa using h
  have hprev := st183_p113
  have hstep := st183_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p115 : ((6453871048113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT183 (i+1))
      = (∑ i ∈ Finset.range 114, stT183 (i+1)) + stT183 115 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 114
    simpa using h
  have hprev := st183_p114
  have hstep := st183_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p116 : ((31353758073509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT183 (i+1))
      = (∑ i ∈ Finset.range 115, stT183 (i+1)) + stT183 116 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 115
    simpa using h
  have hprev := st183_p115
  have hstep := st183_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p117 : ((31200020953217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT183 (i+1))
      = (∑ i ∈ Finset.range 116, stT183 (i+1)) + stT183 117 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 116
    simpa using h
  have hprev := st183_p116
  have hstep := st183_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p118 : ((32105617214237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT183 (i+1))
      = (∑ i ∈ Finset.range 117, stT183 (i+1)) + stT183 118 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 117
    simpa using h
  have hprev := st183_p117
  have hstep := st183_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p119 : ((32293842814577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT183 (i+1))
      = (∑ i ∈ Finset.range 118, stT183 (i+1)) + stT183 119 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 118
    simpa using h
  have hprev := st183_p118
  have hstep := st183_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p120 : ((31408463837613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT183 (i+1))
      = (∑ i ∈ Finset.range 119, stT183 (i+1)) + stT183 120 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 119
    simpa using h
  have hprev := st183_p119
  have hstep := st183_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p121 : ((6228236762177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT183 (i+1))
      = (∑ i ∈ Finset.range 120, stT183 (i+1)) + stT183 121 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 120
    simpa using h
  have hprev := st183_p120
  have hstep := st183_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p122 : ((15993752598493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT183 (i+1))
      = (∑ i ∈ Finset.range 121, stT183 (i+1)) + stT183 122 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 121
    simpa using h
  have hprev := st183_p121
  have hstep := st183_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p123 : ((16185714321917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT183 (i+1))
      = (∑ i ∈ Finset.range 122, stT183 (i+1)) + stT183 123 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 122
    simpa using h
  have hprev := st183_p122
  have hstep := st183_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p124 : ((3159606135571/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT183 (i+1))
      = (∑ i ∈ Finset.range 123, stT183 (i+1)) + stT183 124 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 123
    simpa using h
  have hprev := st183_p123
  have hstep := st183_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p125 : ((15534605084937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT183 (i+1))
      = (∑ i ∈ Finset.range 124, stT183 (i+1)) + stT183 125 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 124
    simpa using h
  have hprev := st183_p124
  have hstep := st183_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p126 : ((15862794465977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT183 (i+1))
      = (∑ i ∈ Finset.range 125, stT183 (i+1)) + stT183 126 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 125
    simpa using h
  have hprev := st183_p125
  have hstep := st183_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p127 : ((3240181720623/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT183 (i+1))
      = (∑ i ∈ Finset.range 126, stT183 (i+1)) + stT183 127 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 126
    simpa using h
  have hprev := st183_p126
  have hstep := st183_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p128 : ((15962875990263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT183 (i+1))
      = (∑ i ∈ Finset.range 127, stT183 (i+1)) + stT183 128 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 127
    simpa using h
  have hprev := st183_p127
  have hstep := st183_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p129 : ((7780630453983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT183 (i+1))
      = (∑ i ∈ Finset.range 128, stT183 (i+1)) + stT183 129 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 128
    simpa using h
  have hprev := st183_p128
  have hstep := st183_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p130 : ((3918959722007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT183 (i+1))
      = (∑ i ∈ Finset.range 129, stT183 (i+1)) + stT183 130 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 129
    simpa using h
  have hprev := st183_p129
  have hstep := st183_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p131 : ((4027665318409/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT183 (i+1))
      = (∑ i ∈ Finset.range 130, stT183 (i+1)) + stT183 131 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 130
    simpa using h
  have hprev := st183_p130
  have hstep := st183_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p132 : ((807341207713/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT183 (i+1))
      = (∑ i ∈ Finset.range 131, stT183 (i+1)) + stT183 132 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 131
    simpa using h
  have hprev := st183_p131
  have hstep := st183_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p133 : ((3145858409279/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT183 (i+1))
      = (∑ i ∈ Finset.range 132, stT183 (i+1)) + stT183 133 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 132
    simpa using h
  have hprev := st183_p132
  have hstep := st183_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p134 : ((31065068438827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT183 (i+1))
      = (∑ i ∈ Finset.range 133, stT183 (i+1)) + stT183 134 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 133
    simpa using h
  have hprev := st183_p133
  have hstep := st183_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p135 : ((6346513380439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT183 (i+1))
      = (∑ i ∈ Finset.range 134, stT183 (i+1)) + stT183 135 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 134
    simpa using h
  have hprev := st183_p134
  have hstep := st183_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p136 : ((32406000816871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT183 (i+1))
      = (∑ i ∈ Finset.range 135, stT183 (i+1)) + stT183 136 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 135
    simpa using h
  have hprev := st183_p135
  have hstep := st183_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p137 : ((6408823738019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT183 (i+1))
      = (∑ i ∈ Finset.range 136, stT183 (i+1)) + stT183 137 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 136
    simpa using h
  have hprev := st183_p136
  have hstep := st183_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p138 : ((31209357348241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT183 (i+1))
      = (∑ i ∈ Finset.range 137, stT183 (i+1)) + stT183 138 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 137
    simpa using h
  have hprev := st183_p137
  have hstep := st183_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p139 : ((15582595649411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT183 (i+1))
      = (∑ i ∈ Finset.range 138, stT183 (i+1)) + stT183 139 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 138
    simpa using h
  have hprev := st183_p138
  have hstep := st183_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p140 : ((799243961707/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT183 (i+1))
      = (∑ i ∈ Finset.range 139, stT183 (i+1)) + stT183 140 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 139
    simpa using h
  have hprev := st183_p139
  have hstep := st183_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p141 : ((32430754452133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT183 (i+1))
      = (∑ i ∈ Finset.range 140, stT183 (i+1)) + stT183 141 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 140
    simpa using h
  have hprev := st183_p140
  have hstep := st183_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p142 : ((31881176677879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT183 (i+1))
      = (∑ i ∈ Finset.range 141, stT183 (i+1)) + stT183 142 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 141
    simpa using h
  have hprev := st183_p141
  have hstep := st183_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p143 : ((31120116941037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT183 (i+1))
      = (∑ i ∈ Finset.range 142, stT183 (i+1)) + stT183 143 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 142
    simpa using h
  have hprev := st183_p142
  have hstep := st183_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p144 : ((97592633533/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT183 (i+1))
      = (∑ i ∈ Finset.range 143, stT183 (i+1)) + stT183 144 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 143
    simpa using h
  have hprev := st183_p143
  have hstep := st183_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p145 : ((2002983308213/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT183 (i+1))
      = (∑ i ∈ Finset.range 144, stT183 (i+1)) + stT183 145 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 144
    simpa using h
  have hprev := st183_p144
  have hstep := st183_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p146 : ((16216960781489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT183 (i+1))
      = (∑ i ∈ Finset.range 145, stT183 (i+1)) + stT183 146 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 145
    simpa using h
  have hprev := st183_p145
  have hstep := st183_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p147 : ((7965879254773/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT183 (i+1))
      = (∑ i ∈ Finset.range 146, stT183 (i+1)) + stT183 147 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 146
    simpa using h
  have hprev := st183_p146
  have hstep := st183_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p148 : ((31117511346867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT183 (i+1))
      = (∑ i ∈ Finset.range 147, stT183 (i+1)) + stT183 148 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 147
    simpa using h
  have hprev := st183_p147
  have hstep := st183_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p149 : ((31195208853369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT183 (i+1))
      = (∑ i ∈ Finset.range 148, stT183 (i+1)) + stT183 149 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 148
    simpa using h
  have hprev := st183_p148
  have hstep := st183_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p150 : ((31985937872601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT183 (i+1))
      = (∑ i ∈ Finset.range 149, stT183 (i+1)) + stT183 150 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 149
    simpa using h
  have hprev := st183_p149
  have hstep := st183_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p151 : ((6489954198277/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT183 (i+1))
      = (∑ i ∈ Finset.range 150, stT183 (i+1)) + stT183 151 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 150
    simpa using h
  have hprev := st183_p150
  have hstep := st183_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p152 : ((31990807151801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT183 (i+1))
      = (∑ i ∈ Finset.range 151, stT183 (i+1)) + stT183 152 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 151
    simpa using h
  have hprev := st183_p151
  have hstep := st183_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p153 : ((31203715096967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT183 (i+1))
      = (∑ i ∈ Finset.range 152, stT183 (i+1)) + stT183 153 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 152
    simpa using h
  have hprev := st183_p152
  have hstep := st183_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p154 : ((31084849757883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT183 (i+1))
      = (∑ i ∈ Finset.range 153, stT183 (i+1)) + stT183 154 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 153
    simpa using h
  have hprev := st183_p153
  have hstep := st183_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p155 : ((31776069506961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT183 (i+1))
      = (∑ i ∈ Finset.range 154, stT183 (i+1)) + stT183 155 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 154
    simpa using h
  have hprev := st183_p154
  have hstep := st183_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p156 : ((32417008248081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT183 (i+1))
      = (∑ i ∈ Finset.range 155, stT183 (i+1)) + stT183 156 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 155
    simpa using h
  have hprev := st183_p155
  have hstep := st183_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p157 : ((8056608861903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT183 (i+1))
      = (∑ i ∈ Finset.range 156, stT183 (i+1)) + stT183 157 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 156
    simpa using h
  have hprev := st183_p156
  have hstep := st183_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p158 : ((7860503814903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT183 (i+1))
      = (∑ i ∈ Finset.range 157, stT183 (i+1)) + stT183 158 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 157
    simpa using h
  have hprev := st183_p157
  have hstep := st183_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p159 : ((968896485227/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT183 (i+1))
      = (∑ i ∈ Finset.range 158, stT183 (i+1)) + stT183 159 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 158
    simpa using h
  have hprev := st183_p158
  have hstep := st183_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p160 : ((15713396435579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT183 (i+1))
      = (∑ i ∈ Finset.range 159, stT183 (i+1)) + stT183 160 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 159
    simpa using h
  have hprev := st183_p159
  have hstep := st183_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p161 : ((8051984191717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT183 (i+1))
      = (∑ i ∈ Finset.range 160, stT183 (i+1)) + stT183 161 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 160
    simpa using h
  have hprev := st183_p160
  have hstep := st183_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p162 : ((3244381417217/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT183 (i+1))
      = (∑ i ∈ Finset.range 161, stT183 (i+1)) + stT183 162 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 161
    simpa using h
  have hprev := st183_p161
  have hstep := st183_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p163 : ((15935231993563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT183 (i+1))
      = (∑ i ∈ Finset.range 162, stT183 (i+1)) + stT183 163 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 162
    simpa using h
  have hprev := st183_p162
  have hstep := st183_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p164 : ((31142301302019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT183 (i+1))
      = (∑ i ∈ Finset.range 163, stT183 (i+1)) + stT183 164 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 163
    simpa using h
  have hprev := st183_p163
  have hstep := st183_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p165 : ((31073310720639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT183 (i+1))
      = (∑ i ∈ Finset.range 164, stT183 (i+1)) + stT183 165 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 164
    simpa using h
  have hprev := st183_p164
  have hstep := st183_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p166 : ((31733436385589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT183 (i+1))
      = (∑ i ∈ Finset.range 165, stT183 (i+1)) + stT183 166 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 165
    simpa using h
  have hprev := st183_p165
  have hstep := st183_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p167 : ((16197482256649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT183 (i+1))
      = (∑ i ∈ Finset.range 166, stT183 (i+1)) + stT183 167 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 166
    simpa using h
  have hprev := st183_p166
  have hstep := st183_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p168 : ((32343190321979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT183 (i+1))
      = (∑ i ∈ Finset.range 167, stT183 (i+1)) + stT183 168 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 167
    simpa using h
  have hprev := st183_p167
  have hstep := st183_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p169 : ((31640031649493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT183 (i+1))
      = (∑ i ∈ Finset.range 168, stT183 (i+1)) + stT183 169 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 168
    simpa using h
  have hprev := st183_p168
  have hstep := st183_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p170 : ((31035049657493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT183 (i+1))
      = (∑ i ∈ Finset.range 169, stT183 (i+1)) + stT183 170 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 169
    simpa using h
  have hprev := st183_p169
  have hstep := st183_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p171 : ((973758488407/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT183 (i+1))
      = (∑ i ∈ Finset.range 170, stT183 (i+1)) + stT183 171 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 170
    simpa using h
  have hprev := st183_p170
  have hstep := st183_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p172 : ((7969819868189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT183 (i+1))
      = (∑ i ∈ Finset.range 171, stT183 (i+1)) + stT183 172 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 171
    simpa using h
  have hprev := st183_p171
  have hstep := st183_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p173 : ((32449991209431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT183 (i+1))
      = (∑ i ∈ Finset.range 172, stT183 (i+1)) + stT183 173 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 172
    simpa using h
  have hprev := st183_p172
  have hstep := st183_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p174 : ((8073790594091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT183 (i+1))
      = (∑ i ∈ Finset.range 173, stT183 (i+1)) + stT183 174 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 173
    simpa using h
  have hprev := st183_p173
  have hstep := st183_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p175 : ((394709130981/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT183 (i+1))
      = (∑ i ∈ Finset.range 174, stT183 (i+1)) + stT183 175 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 174
    simpa using h
  have hprev := st183_p174
  have hstep := st183_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p176 : ((31013132181517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT183 (i+1))
      = (∑ i ∈ Finset.range 175, stT183 (i+1)) + stT183 176 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 175
    simpa using h
  have hprev := st183_p175
  have hstep := st183_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p177 : ((31156769477179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT183 (i+1))
      = (∑ i ∈ Finset.range 176, stT183 (i+1)) + stT183 177 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 176
    simpa using h
  have hprev := st183_p176
  have hstep := st183_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p178 : ((31861466530883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT183 (i+1))
      = (∑ i ∈ Finset.range 177, stT183 (i+1)) + stT183 178 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 177
    simpa using h
  have hprev := st183_p177
  have hstep := st183_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p179 : ((32443675044653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT183 (i+1))
      = (∑ i ∈ Finset.range 178, stT183 (i+1)) + stT183 179 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 178
    simpa using h
  have hprev := st183_p178
  have hstep := st183_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p180 : ((32349648385253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT183 (i+1))
      = (∑ i ∈ Finset.range 179, stT183 (i+1)) + stT183 180 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 179
    simpa using h
  have hprev := st183_p179
  have hstep := st183_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p181 : ((31674137429483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT183 (i+1))
      = (∑ i ∈ Finset.range 180, stT183 (i+1)) + stT183 181 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 180
    simpa using h
  have hprev := st183_p180
  have hstep := st183_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p182 : ((31053161913233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT183 (i+1))
      = (∑ i ∈ Finset.range 181, stT183 (i+1)) + stT183 182 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 181
    simpa using h
  have hprev := st183_p181
  have hstep := st183_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p183 : ((31060299831209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT183 (i+1))
      = (∑ i ∈ Finset.range 182, stT183 (i+1)) + stT183 183 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 182
    simpa using h
  have hprev := st183_p182
  have hstep := st183_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p184 : ((15841684486683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT183 (i+1))
      = (∑ i ∈ Finset.range 183, stT183 (i+1)) + stT183 184 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 183
    simpa using h
  have hprev := st183_p183
  have hstep := st183_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p185 : ((1617610429433/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT183 (i+1))
      = (∑ i ∈ Finset.range 184, stT183 (i+1)) + stT183 185 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 184
    simpa using h
  have hprev := st183_p184
  have hstep := st183_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p186 : ((6493249872289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT183 (i+1))
      = (∑ i ∈ Finset.range 185, stT183 (i+1)) + stT183 186 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 185
    simpa using h
  have hprev := st183_p185
  have hstep := st183_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p187 : ((15964521160729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT183 (i+1))
      = (∑ i ∈ Finset.range 186, stT183 (i+1)) + stT183 187 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 186
    simpa using h
  have hprev := st183_p186
  have hstep := st183_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p188 : ((15609462412329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT183 (i+1))
      = (∑ i ∈ Finset.range 187, stT183 (i+1)) + stT183 188 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 187
    simpa using h
  have hprev := st183_p187
  have hstep := st183_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p189 : ((3869503987673/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT183 (i+1))
      = (∑ i ∈ Finset.range 188, stT183 (i+1)) + stT183 189 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 188
    simpa using h
  have hprev := st183_p188
  have hstep := st183_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p190 : ((1960200331649/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT183 (i+1))
      = (∑ i ∈ Finset.range 189, stT183 (i+1)) + stT183 190 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 189
    simpa using h
  have hprev := st183_p189
  have hstep := st183_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p191 : ((3208667004671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT183 (i+1))
      = (∑ i ∈ Finset.range 190, stT183 (i+1)) + stT183 191 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 190
    simpa using h
  have hprev := st183_p190
  have hstep := st183_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p192 : ((3251145501491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT183 (i+1))
      = (∑ i ∈ Finset.range 191, stT183 (i+1)) + stT183 192 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 191
    simpa using h
  have hprev := st183_p191
  have hstep := st183_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p193 : ((16142064242159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT183 (i+1))
      = (∑ i ∈ Finset.range 192, stT183 (i+1)) + stT183 193 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 192
    simpa using h
  have hprev := st183_p192
  have hstep := st183_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p194 : ((31599009646937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT183 (i+1))
      = (∑ i ∈ Finset.range 193, stT183 (i+1)) + stT183 194 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 193
    simpa using h
  have hprev := st183_p193
  have hstep := st183_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p195 : ((31023336256277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT183 (i+1))
      = (∑ i ∈ Finset.range 194, stT183 (i+1)) + stT183 195 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 194
    simpa using h
  have hprev := st183_p194
  have hstep := st183_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p196 : ((15512489913031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT183 (i+1))
      = (∑ i ∈ Finset.range 195, stT183 (i+1)) + stT183 196 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 195
    simpa using h
  have hprev := st183_p195
  have hstep := st183_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p197 : ((15798813794281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT183 (i+1))
      = (∑ i ∈ Finset.range 196, stT183 (i+1)) + stT183 197 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 196
    simpa using h
  have hprev := st183_p196
  have hstep := st183_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p198 : ((32278699356719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT183 (i+1))
      = (∑ i ∈ Finset.range 197, stT183 (i+1)) + stT183 198 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 197
    simpa using h
  have hprev := st183_p197
  have hstep := st183_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p199 : ((6505601993779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT183 (i+1))
      = (∑ i ∈ Finset.range 198, stT183 (i+1)) + stT183 199 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 198
    simpa using h
  have hprev := st183_p198
  have hstep := st183_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p200 : ((3215365691649/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT183 (i+1))
      = (∑ i ∈ Finset.range 199, stT183 (i+1)) + stT183 200 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 199
    simpa using h
  have hprev := st183_p199
  have hstep := st183_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p201 : ((3931476796259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT183 (i+1))
      = (∑ i ∈ Finset.range 200, stT183 (i+1)) + stT183 201 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 200
    simpa using h
  have hprev := st183_p200
  have hstep := st183_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p202 : ((774140281643/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT183 (i+1))
      = (∑ i ∈ Finset.range 201, stT183 (i+1)) + stT183 202 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 201
    simpa using h
  have hprev := st183_p201
  have hstep := st183_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p203 : ((7766030803079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT183 (i+1))
      = (∑ i ∈ Finset.range 202, stT183 (i+1)) + stT183 203 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 202
    simpa using h
  have hprev := st183_p202
  have hstep := st183_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p204 : ((1979246253221/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT183 (i+1))
      = (∑ i ∈ Finset.range 203, stT183 (i+1)) + stT183 204 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 203
    simpa using h
  have hprev := st183_p203
  have hstep := st183_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p205 : ((4040065289077/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT183 (i+1))
      = (∑ i ∈ Finset.range 204, stT183 (i+1)) + stT183 205 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 204
    simpa using h
  have hprev := st183_p204
  have hstep := st183_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p206 : ((16268528587377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT183 (i+1))
      = (∑ i ∈ Finset.range 205, stT183 (i+1)) + stT183 206 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 205
    simpa using h
  have hprev := st183_p205
  have hstep := st183_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p207 : ((804046986381/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT183 (i+1))
      = (∑ i ∈ Finset.range 206, stT183 (i+1)) + stT183 207 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 206
    simpa using h
  have hprev := st183_p206
  have hstep := st183_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p208 : ((3934168855857/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT183 (i+1))
      = (∑ i ∈ Finset.range 207, stT183 (i+1)) + stT183 208 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 207
    simpa using h
  have hprev := st183_p207
  have hstep := st183_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p209 : ((3871430305357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT183 (i+1))
      = (∑ i ∈ Finset.range 208, stT183 (i+1)) + stT183 209 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 208
    simpa using h
  have hprev := st183_p208
  have hstep := st183_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p210 : ((242296444737/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT183 (i+1))
      = (∑ i ∈ Finset.range 209, stT183 (i+1)) + stT183 210 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 209
    simpa using h
  have hprev := st183_p209
  have hstep := st183_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p211 : ((493221818133/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT183 (i+1))
      = (∑ i ∈ Finset.range 210, stT183 (i+1)) + stT183 211 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 210
    simpa using h
  have hprev := st183_p210
  have hstep := st183_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p212 : ((16117788813891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT183 (i+1))
      = (∑ i ∈ Finset.range 211, stT183 (i+1)) + stT183 212 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 211
    simpa using h
  have hprev := st183_p211
  have hstep := st183_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p213 : ((16277227950363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT183 (i+1))
      = (∑ i ∈ Finset.range 212, stT183 (i+1)) + stT183 213 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 212
    simpa using h
  have hprev := st183_p212
  have hstep := st183_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p214 : ((2019081276543/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT183 (i+1))
      = (∑ i ∈ Finset.range 213, stT183 (i+1)) + stT183 214 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 213
    simpa using h
  have hprev := st183_p213
  have hstep := st183_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p215 : ((7915842816737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT183 (i+1))
      = (∑ i ∈ Finset.range 214, stT183 (i+1)) + stT183 215 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 214
    simpa using h
  have hprev := st183_p214
  have hstep := st183_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p216 : ((3883464214659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT183 (i+1))
      = (∑ i ∈ Finset.range 215, stT183 (i+1)) + stT183 216 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 215
    simpa using h
  have hprev := st183_p215
  have hstep := st183_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p217 : ((30918892564457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT183 (i+1))
      = (∑ i ∈ Finset.range 216, stT183 (i+1)) + stT183 217 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 216
    simpa using h
  have hprev := st183_p216
  have hstep := st183_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p218 : ((15656304924401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT183 (i+1))
      = (∑ i ∈ Finset.range 217, stT183 (i+1)) + stT183 218 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 217
    simpa using h
  have hprev := st183_p217
  have hstep := st183_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p219 : ((6396802939779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT183 (i+1))
      = (∑ i ∈ Finset.range 218, stT183 (i+1)) + stT183 219 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 218
    simpa using h
  have hprev := st183_p218
  have hstep := st183_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p220 : ((16245232785753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT183 (i+1))
      = (∑ i ∈ Finset.range 219, stT183 (i+1)) + stT183 220 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 219
    simpa using h
  have hprev := st183_p219
  have hstep := st183_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p221 : ((16251940670937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT183 (i+1))
      = (∑ i ∈ Finset.range 220, stT183 (i+1)) + stT183 221 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 220
    simpa using h
  have hprev := st183_p220
  have hstep := st183_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p222 : ((16009755009801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT183 (i+1))
      = (∑ i ∈ Finset.range 221, stT183 (i+1)) + stT183 222 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 221
    simpa using h
  have hprev := st183_p221
  have hstep := st183_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p223 : ((1959434178847/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT183 (i+1))
      = (∑ i ∈ Finset.range 222, stT183 (i+1)) + stT183 223 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 222
    simpa using h
  have hprev := st183_p222
  have hstep := st183_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p224 : ((1546173831587/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT183 (i+1))
      = (∑ i ∈ Finset.range 223, stT183 (i+1)) + stT183 224 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 223
    simpa using h
  have hprev := st183_p223
  have hstep := st183_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p225 : ((242218129307/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT183 (i+1))
      = (∑ i ∈ Finset.range 224, stT183 (i+1)) + stT183 225 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 224
    simpa using h
  have hprev := st183_p224
  have hstep := st183_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p226 : ((7884530666719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT183 (i+1))
      = (∑ i ∈ Finset.range 225, stT183 (i+1)) + stT183 226 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 225
    simpa using h
  have hprev := st183_p225
  have hstep := st183_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p227 : ((32192279427277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT183 (i+1))
      = (∑ i ∈ Finset.range 226, stT183 (i+1)) + stT183 227 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 226
    simpa using h
  have hprev := st183_p226
  have hstep := st183_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p228 : ((32564389473761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT183 (i+1))
      = (∑ i ∈ Finset.range 227, stT183 (i+1)) + stT183 228 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 227
    simpa using h
  have hprev := st183_p227
  have hstep := st183_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p229 : ((32430371415647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT183 (i+1))
      = (∑ i ∈ Finset.range 228, stT183 (i+1)) + stT183 229 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 228
    simpa using h
  have hprev := st183_p228
  have hstep := st183_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p230 : ((15937467288553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT183 (i+1))
      = (∑ i ∈ Finset.range 229, stT183 (i+1)) + stT183 230 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 229
    simpa using h
  have hprev := st183_p229
  have hstep := st183_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p231 : ((15616743980489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT183 (i+1))
      = (∑ i ∈ Finset.range 230, stT183 (i+1)) + stT183 231 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 230
    simpa using h
  have hprev := st183_p230
  have hstep := st183_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p232 : ((6177430603257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT183 (i+1))
      = (∑ i ∈ Finset.range 231, stT183 (i+1)) + stT183 232 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 231
    simpa using h
  have hprev := st183_p231
  have hstep := st183_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p233 : ((31037416809813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT183 (i+1))
      = (∑ i ∈ Finset.range 232, stT183 (i+1)) + stT183 233 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 232
    simpa using h
  have hprev := st183_p232
  have hstep := st183_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p234 : ((31592780059773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT183 (i+1))
      = (∑ i ∈ Finset.range 233, stT183 (i+1)) + stT183 234 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 233
    simpa using h
  have hprev := st183_p233
  have hstep := st183_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p235 : ((32228661566237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT183 (i+1))
      = (∑ i ∈ Finset.range 234, stT183 (i+1)) + stT183 235 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 234
    simpa using h
  have hprev := st183_p234
  have hstep := st183_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p236 : ((32579307523549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT183 (i+1))
      = (∑ i ∈ Finset.range 235, stT183 (i+1)) + stT183 236 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 235
    simpa using h
  have hprev := st183_p235
  have hstep := st183_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p237 : ((32447133669519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT183 (i+1))
      = (∑ i ∈ Finset.range 236, stT183 (i+1)) + stT183 237 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 236
    simpa using h
  have hprev := st183_p236
  have hstep := st183_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p238 : ((31910443444659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT183 (i+1))
      = (∑ i ∈ Finset.range 237, stT183 (i+1)) + stT183 238 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 237
    simpa using h
  have hprev := st183_p237
  have hstep := st183_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p239 : ((31273096039701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT183 (i+1))
      = (∑ i ∈ Finset.range 238, stT183 (i+1)) + stT183 239 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 238
    simpa using h
  have hprev := st183_p238
  have hstep := st183_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p240 : ((30890265376857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT183 (i+1))
      = (∑ i ∈ Finset.range 239, stT183 (i+1)) + stT183 240 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 239
    simpa using h
  have hprev := st183_p239
  have hstep := st183_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p241 : ((30971246092553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT183 (i+1))
      = (∑ i ∈ Finset.range 240, stT183 (i+1)) + stT183 241 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 240
    simpa using h
  have hprev := st183_p240
  have hstep := st183_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p242 : ((31468243539681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT183 (i+1))
      = (∑ i ∈ Finset.range 241, stT183 (i+1)) + stT183 242 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 241
    simpa using h
  have hprev := st183_p241
  have hstep := st183_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p243 : ((32108241788181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT183 (i+1))
      = (∑ i ∈ Finset.range 242, stT183 (i+1)) + stT183 243 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 242
    simpa using h
  have hprev := st183_p242
  have hstep := st183_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p244 : ((32545306928293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT183 (i+1))
      = (∑ i ∈ Finset.range 243, stT183 (i+1)) + stT183 244 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 243
    simpa using h
  have hprev := st183_p243
  have hstep := st183_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p245 : ((32547245278077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT183 (i+1))
      = (∑ i ∈ Finset.range 244, stT183 (i+1)) + stT183 245 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 244
    simpa using h
  have hprev := st183_p244
  have hstep := st183_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p246 : ((32116202421149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT183 (i+1))
      = (∑ i ∈ Finset.range 245, stT183 (i+1)) + stT183 246 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 245
    simpa using h
  have hprev := st183_p245
  have hstep := st183_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p247 : ((7870560124421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT183 (i+1))
      = (∑ i ∈ Finset.range 246, stT183 (i+1)) + stT183 247 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 246
    simpa using h
  have hprev := st183_p246
  have hstep := st183_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p248 : ((3097797731357/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT183 (i+1))
      = (∑ i ∈ Finset.range 247, stT183 (i+1)) + stT183 248 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 247
    simpa using h
  have hprev := st183_p247
  have hstep := st183_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p249 : ((1543191601701/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT183 (i+1))
      = (∑ i ∈ Finset.range 248, stT183 (i+1)) + stT183 249 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 248
    simpa using h
  have hprev := st183_p248
  have hstep := st183_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_p250 : ((6239136866959/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT183 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT183 (i+1))
      = (∑ i ∈ Finset.range 249, stT183 (i+1)) + stT183 250 := by
    have h := Finset.sum_range_succ (fun i => stT183 (i+1)) 249
    simpa using h
  have hprev := st183_p249
  have hstep := st183_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st183_s250 :
    |Real.sin (((183 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))
      - ((-425627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -636481/2500000) (δ := 9157/1000000000) (ψ := -147111/1000000) 183 161
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 183`** (evaluated boundary). -/
theorem station_183_sign : hardyG ((((183:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 183 250 (by norm_num) (by norm_num)
    ((-147111/1000000 : ℚ) : ℝ)
  have hchain := st183_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT183 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((183 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-147111/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st183_c250
  have hsinb := abs_le.mp st183_s250
  have hbdy_lo : ((39340707020769/535828000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((183 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ))) / 2
          - ((((183:ℕ)):ℝ))
            * Real.sin (((183 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-147111/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((183:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((183:ℝ) * Real.log (250:ℝ) - ((-147111/1000000 : ℚ) : ℝ))) / 2
        - ((183:ℝ)) * Real.sin ((183:ℝ) * Real.log (250:ℝ) - ((-147111/1000000 : ℚ) : ℝ))
        ≥ ((311015859/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((183:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((311015859/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((311015859/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((311015859/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((183:ℕ)):ℝ))+1) * (((((183:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((35322904771/46875000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6239136866959/2000000000000 : ℚ) : ℝ) + ((39340707020769/535828000000000 : ℚ) : ℝ)
      - ((35322904771/46875000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-147111/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((183:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-147111/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((183:ℕ)):ℝ)))).re
      - Real.sin ((-147111/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((183:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((183:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((183:ℕ)):ℝ))
      = (((((183:ℕ)):ℝ)) * (Real.log ((((183:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((183:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_183
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
  have hθwin : |(((-147111/1000000 : ℚ) : ℝ) + ((35:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((183:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((183:ℕ)):ℝ)))
    (φ := ((-147111/1000000 : ℚ) : ℝ) + ((35:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-147111/1000000 : ℚ) : ℝ) + ((35:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-147111/1000000 : ℚ)) : ℝ) - Real.pi) + ((35:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-147111/1000000 : ℚ)) : ℝ) - Real.pi) 35).1,
    (cos_sin_shift ((((-147111/1000000 : ℚ)) : ℝ) - Real.pi) 35).2]
  exact cos_sin_flip ((-147111/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_183_sign
end AxiomAudit
